(** {0} Normalization by evaluation. *)

(** {0} Evaluation *)

module S = Syntax
module V = Value

module TB = TermBuilder

module Idx = S.Idx
module Lvl = V.Lvl

let rec eval_tm (env : V.env) (tm : S.tm) : V.tm =
  match tm with
  | S.Var ix ->
    Lazy.force (V.Env.nth_tm env ix)
  | S.DimZero ->
    V.DimZero
  | S.DimSucc tm ->
    V.DimSucc (eval_tm env tm)
  | S.Lam body ->
    V.Lam { env; body }
  | S.App (tm, arg) ->
    do_app (eval_tm env tm) (eval_tm_lazy env arg)
  | S.Tuple tms ->
    V.Tuple (List.map (eval_tm_lazy env) tms)
  | S.Proj (tm, ix) ->
    do_proj (eval_tm env tm) ix
  | S.Pt ->
    V.pt
  | S.Compound tele ->
    V.Compound { env; body = tele }
  | S.AppZero tm ->
    do_app_zero (eval_tm env tm)
  | S.Inst (mtm, arg) ->
    do_inst (eval_meta_tm env mtm) (eval_tm_lazy env arg)
  | S.DimRec {mot; zero; succ; scrut} ->
    do_dim_rec (eval_tp env mot) (eval_tm env zero) (eval_tm env succ) (eval_tm env scrut)

and eval_meta_tm (env : V.env) (mtm : S.meta_tm) : V.meta_tm =
  match mtm with
  | S.MetaAbs body ->
    V.MetaAbs { env; body }
  | S.AppOne tm ->
    do_app_one (eval_tm env tm)
  | S.MetaAppZero mtm ->
    do_meta_app_zero (eval_meta_tm env mtm)
  | S.MetaAppOne mtm ->
    do_meta_app_one (eval_meta_tm env mtm)

and eval_tp (env : V.env) (tp : S.tp) : V.tp =
  match tp with
  | S.TpVar ix ->
    Lazy.force (V.Env.nth_tp env ix)
  | S.Dim ->
    V.Dim
  | S.Pi (base, fam) ->
    V.Pi (eval_tp env base, { env; body = fam })
  | S.Record tele ->
    V.Record {env; body = tele}
  | S.TpInst (mtp, tm) ->
    do_tp_inst (eval_meta_tp env mtp) (eval_tm_lazy env tm)
  | S.ShapeUniv tm ->
    V.ShapeUniv (eval_tm env tm)
  | S.ElShape tm ->
    do_el_shape (eval_tm env tm)
  | S.PointUniv tm ->
    V.PointUniv (eval_tm env tm)
  | S.ElPoint _ ->
    failwith "todo: implement evaluation for el-point"

and eval_meta_tp (env : V.env) (mtp : S.meta_tp) : V.meta_tp =
  match mtp with
  | S.TpMetaAbs body ->
    V.TpMetaAbs {env; body}

(** Lazily evaluate a term. *)
and eval_tm_lazy (env : V.env) (tm : S.tm) : V.tm Lazy.t =
  Lazy.from_fun @@ fun () -> eval_tm env tm

and do_app (v : V.tm) (arg : V.tm Lazy.t) : V.tm =
  match v with
  | V.Lam clo ->
    eval_tm (V.Env.extend_tm clo.env arg) clo.body
  | V.Neu neu ->
    V.Neu (V.Neu.push neu (V.App arg))
  | _ ->
    failwith @@ Format.asprintf "bad do_app: %a" V.dump_tm v

and do_apps (v : V.tm) (args : V.tm Lazy.t List.t) : V.tm =
  List.fold_left do_app v args

(** Project the nth field out of a tuple. *)
and do_proj (v : V.tm) (ix : Idx.t) : V.tm =
  match v with
  | V.Tuple vs ->
    Lazy.force (List.nth vs ix)
  | V.Neu neu ->
    V.Neu (V.Neu.push neu (V.Proj ix))
  | _ ->
    failwith @@ Format.asprintf "bad do_proj: %a" V.dump_tm v

and do_app_zero (v : V.tm) : V.tm =
  match v with
  | V.Compound tele_clo ->
    V.Compound { tele_clo with body = List.map (fun tm -> S.AppZero tm) tele_clo.body }
  | V.Neu neu ->
    V.Neu { neu with zeros = neu.zeros + 1 }
  | _ ->
    failwith @@ Format.asprintf "bad do_app_zero: %a" V.dump_tm v

and do_app_one (v : V.tm) : V.meta_tm =
  match v with
  | V.Compound tele ->
    splice_meta_tm @@
    Splice.tm_tele tele @@ fun tele ->
    Splice.build @@
    TB.meta_abs @@ fun x ->
    TB.compound (TB.Tele.map (fun tm -> TB.inst (TB.app_one tm) x) tele)
  | V.Neu neu ->
    V.MetaNeu { meta_hd = V.AppOne neu; meta_spine = [] }
  | _ ->
    failwith @@ Format.asprintf "bad do_app_one: %a" V.dump_tm v

and do_meta_app_zero (v : V.meta_tm) : V.meta_tm =
  match v with
  | V.MetaNeu neu ->
    V.MetaNeu (V.MetaNeu.push neu V.MetaAppZero)
  | V.MetaAbs clo ->
    splice_meta_tm @@
    Splice.tm_clo clo @@ fun tm ->
    Splice.build @@
    TB.meta_abs @@ fun x ->
    TB.app_zero (tm x)

and do_meta_app_one (v : V.meta_tm) : V.meta_tm =
  match v with
  | V.MetaNeu neu ->
    V.MetaNeu (V.MetaNeu.push neu V.MetaAppOne)
  | V.MetaAbs clo ->
    splice_meta_tm @@
    Splice.tm_clo clo @@ fun tm ->
    Splice.build @@
    TB.meta_abs @@ fun omega ->
    TB.inst (TB.app_one (tm (TB.proj omega 0))) (TB.tuple [TB.proj omega 2; TB.proj omega 1])

and do_inst (mv : V.meta_tm) (arg : V.tm Lazy.t) : V.tm =
  match mv with
  | V.MetaAbs clo ->
    eval_tm (V.Env.extend_tm clo.env arg) clo.body
  | V.MetaNeu neu ->
    V.Neu { hd = V.Inst (neu, arg); spine = []; zeros = 0 }

and do_dim_rec (mot : V.tp) (zero : V.tm) (succ : V.tm) (scrut : V.tm) : V.tm =
  match scrut with
  | V.DimZero ->
    zero
  | V.DimSucc d ->
    do_apps succ [Lazy.from_val d; Lazy.from_fun @@ fun () -> do_dim_rec mot zero succ d]
  | V.Neu neu ->
    V.Neu (V.Neu.push neu (V.DimRec { mot; zero; succ }))
  | _ ->
    failwith "bad do_dim_rec"

and do_tp_inst (mtp : V.meta_tp) (arg : V.tm Lazy.t) : V.tp =
  match mtp with
  | V.TpMetaAbs clo ->
    eval_tp (V.Env.extend_tm clo.env arg) clo.body

(** Decode a shape to a type. *)
and do_el_shape (v : V.tm) : V.tp =
  match v with
  | V.Compound tele_clo ->
    V.Record { tele_clo with body = List.map (fun tm -> S.ElShape tm) tele_clo.body }
  | V.Neu neu ->
    V.ElShape neu
  | _ ->
    failwith "bad do_el_shape"

(* (\** Evaluate a term. *\) *)
(* let rec eval_tm (env : V.env) (tm : S.tm) : V.tm = *)
(*   match tm with *)
(*   | S.Var ix -> *)
(*     Lazy.force (V.Env.nth_tm env ix) *)
(*   | S.DimZero -> *)
(*     V.DimZero *)
(*   | S.DimSucc tm -> *)
(*     V.DimSucc (eval_tm env tm) *)
(*   | S.Tuple tms -> *)
(*     V.Tuple (List.map (eval_tm_lazy env) tms) *)
(*   | S.Proj (tm, ix) -> *)
(*     do_proj (eval_tm env tm) ix *)
(*   | S.Pt -> *)
(*     V.pt *)
(*   | S.Compound tms -> *)
(*     V.Compound (eval_tm_tele env tms) *)
(*   | S.MetaAbs tm -> *)
(*     V.MetaAbs {body = tm; env} *)
(*   | S.Inst (tm, arg) -> *)
(*     do_inst (eval_tm env tm) (eval_tm_lazy env arg) *)
(*   | S.ZeroAct tm -> *)
(*     do_zero_act (eval_tm env tm) *)
(*   | S.OneAct tm -> *)
(*     do_one_act (eval_tm env tm) *)
(*   | S.DimRec elim -> *)
(*     do_dim_rec (eval_tp env elim.mot) (eval_tm env elim.zero) (eval_tm env elim.succ) (eval_tm env elim.scrut) *)

(* (\** Evaluate a type. *\) *)
(* and eval_tp (env : V.env) (tp : S.tp) : V.tp = *)
(*   match tp with *)
(*   | S.TpVar ix -> *)
(*     Lazy.force (V.Env.nth_tp env ix) *)
(*   | S.Dim -> *)
(*     V.Dim *)
(*   | S.Record tele -> *)
(*     V.Record (eval_tp_tele env tele) *)
(*   | S.TpMetaAbs body -> *)
(*     V.TpMetaAbs { body; env } *)
(*   | S.TpInst (tp, arg) -> *)
(*     do_tp_inst (eval_tp env tp) (eval_tp env arg) *)
(*   | S.ShapeUniv dim -> *)
(*     V.ShapeUniv (eval_tm env dim) *)
(*   | S.ElShape tm -> *)
(*     do_el_shape (eval_tm env tm) *)
(*   | S.PointUniv dim -> *)
(*     V.PointUniv (eval_tm env dim) *)
(*   | S.ElPoint _ -> failwith "el point not implemented" *)

(* (\** Lazily evaluate a term. *\) *)
(* and eval_tm_lazy (env : V.env) (tm : S.tm) : V.tm Lazy.t = *)
(*   Lazy.from_fun @@ fun () -> eval_tm env tm *)

(* (\** Evaluate a telescope of terms. *\) *)
(* and eval_tm_tele (env : V.env) (tms : S.tm List.t) : (S.tm, V.tm) V.tele = *)
(*   match tms with *)
(*   | [] -> Nil *)
(*   | (tm :: tms) -> Cons (eval_tm env tm, { body = tms; env }) *)

(* (\** Evaluate a telescope of types. *\) *)
(* and eval_tp_tele (env : V.env) (tms : S.tp List.t) : (S.tp, V.tp) V.tele = *)
(*   match tms with *)
(*   | [] -> Nil *)
(*   | (tp :: tps) -> Cons (eval_tp env tp, { body = tps; env }) *)

(* (\** Project the nth field out of a tuple. *\) *)
(* and do_proj (v : V.tm) (ix : Idx.t) : V.tm = *)
(*   match v with *)
(*   | V.Tuple vs -> *)
(*     Lazy.force (List.nth vs ix) *)
(*   | V.Neu neu -> *)
(*     V.Neu (V.Neu.push neu (V.Proj ix)) *)
(*   | _ -> *)
(*     failwith @@ Format.asprintf "bad do_proj: %a" SExpr.dump (V.tm_sexpr v) *)

(* (\** Instantiate a term-level meta-abstraction. *\) *)
(* and do_inst (v : V.tm) (arg : V.tm Lazy.t) : V.tm = *)
(*   match v with *)
(*   | V.MetaAbs clo -> *)
(*     eval_tm (V.Env.extend_tm clo.env arg) clo.body *)
(*   | V.Neu neu -> *)
(*     V.Neu (V.Neu.push neu (V.Inst arg)) *)
(*   | _ -> *)
(*     failwith @@ Format.asprintf "bad do_inst: %a" SExpr.dump (V.tm_sexpr v) *)

(* and do_insts (v : V.tm) (args : V.tm Lazy.t List.t) : V.tm = *)
(*   List.fold_left do_inst v args *)

(* and do_zero_act (v : V.tm) : V.tm = *)
(*   match v with *)
(*   | V.Compound tele -> *)
(*     V.Compound (do_zero_act_tele tele) *)
(*   | V.MetaAbs clo -> *)
(*     V.MetaAbs (do_zero_act_clo clo) *)
(*   | V.Neu neu -> *)
(*     V.Neu { hd = do_zero_act_hd neu.hd; spine = List.map do_zero_act_frm neu.spine } *)
(*     (\* V.Neu (V.Neu.push neu V.ZeroAct) *\) *)
(*   | _ -> *)
(*     failwith @@ Format.asprintf "bad do_zero_act: %a" SExpr.dump (V.tm_sexpr v) *)

(* and do_zero_act_tele (tele : (S.tm, V.tm) V.tele) : (S.tm, V.tm) V.tele = *)
(*   match tele with *)
(*   | Nil -> Nil *)
(*   | Cons (v, clo) -> *)
(*     Cons (do_zero_act v, { clo with body = List.map (fun tm -> S.ZeroAct tm) clo.body }) *)

(* and do_zero_act_clo (clo : S.tm V.clo) : S.tm V.clo = *)
(*   { clo with body = S.ZeroAct clo.body } *)

(* and do_zero_act_hd (hd : V.hd) : V.hd = *)
(*   match hd with *)
(*   | V.Var (lvl, ds) -> V.Var (lvl, false :: ds) *)
(*   | V.Pt ds -> V.Pt (false :: ds) *)

(* and do_zero_act_frm (frm : V.frm) : V.frm = *)
(*   match frm with *)
(*   | V.Proj i -> V.Proj i *)
(*   | V.Inst arg -> V.Inst arg *)
(*   | V.DimRec { mot; zero; succ } -> *)
(*     let mot = *)
(*       splice_tp @@ *)
(*       Splice.tp mot @@ fun mot -> *)
(*       Splice.build @@ *)
(*       __ *)
(*       (\* TB.tp_meta_abs @@ fun d -> __ *\) *)
(*       (\* TB.meta_abs @@ fun d -> __ *\) *)
(*     and zero = do_zero_act zero *)
(*     and succ = *)
(*       splice_tm @@ *)
(*       Splice.tm succ @@ fun succ -> *)
(*       Splice.build @@ *)
(*       TB.meta_abs @@ fun d -> TB.zero_act (TB.inst succ d) *)
(*     in V.DimRec { mot; zero; succ } *)

(* and do_one_act (v : V.tm) : V.tm = *)
(*   match v with *)
(*   | V.Compound tele -> *)
(*     splice_tm @@ *)
(*     Splice.shape_tele tele @@ fun tele -> *)
(*     Splice.build @@ *)
(*     TB.meta_abs @@ fun x -> TB.compound (TB.inst_tele tele x) *)
(*   | V.MetaAbs clo -> *)
(*     __ *)
(*   | V.Neu neu -> *)
(*     __ *)
(*     (\* V.Neu (V.Neu.push neu V.OneAct) *\) *)
(*   | _ -> *)
(*     failwith @@ Format.asprintf "bad do_one_act: %a" SExpr.dump (V.tm_sexpr v) *)

(* (\* (\\** Apply a digit to a shape. *\\) *\) *)
(* (\* and do_digit (d : bool) (v : V.tm) : V.tm = *\) *)
(* (\*   match v with *\) *)
(* (\*   | V.Compound vs -> *\) *)
(* (\*     V.Compound (do_tele_digit d vs) *\) *)
(* (\*   | V.MetaAbs clo -> *\) *)
(* (\*     V.MetaAbs (do_clo_digit d clo) *\) *)
(* (\*   | V.Neu neu -> *\) *)
(* (\*     V.Neu (V.Neu.push neu (Digit d)) *\) *)
(* (\*   | _ -> *\) *)
(* (\*     failwith @@ Format.asprintf "bad do_digit: %a" SExpr.dump (V.tm_sexpr v) *\) *)

(* (\* (\\** Apply a digit to a telescope of shapes. *\\) *\) *)
(* (\* and do_tele_digit (d : bool) (tele : (S.tm, V.tm) V.tele) : (S.tm, V.tm) V.tele = *\) *)
(* (\*   match tele with *\) *)
(* (\*   | Nil -> Nil *\) *)
(* (\*   | Cons (v, clo) -> *\) *)
(* (\*     Cons (do_digit d v, { clo with body = List.map (fun tm -> S.Digit (d, tm)) clo.body }) *\) *)

(* (\* and do_clo_digit (d : bool) (clo : S.tm V.clo) : S.tm V.clo = *\) *)
(* (\*   match d with *\) *)
(* (\*   | false -> *\) *)
(* (\*     (\\* When we apply a 0 to a closure, we change the types, *\) *)
(* (\*        but nothing in the body of the closure needs to change. *\\) *\) *)
(* (\*     clo *\) *)
(* (\*   | true -> *\) *)
(* (\*     (\\* When we apply a 1 to a closure, we need to get the 0th field out of *\) *)
(* (\*        the newly compound shape argument, which we do by evaluating the body *\) *)
(* (\*        of the closure with a projection out of the new argument. We then need to *\) *)
(* (\*        re-quote the body. *\) *)

(* (\*        Note that we could also accomplish this by substituting for the bound variable *\) *)
(* (\*        in the body of the closure. *\\) *\) *)
(* (\*     let var = Lazy.from_fun @@ fun () -> do_proj (V.var clo.env.tmlen) 0 in *\) *)
(* (\*     let body = quote_tm clo.env.tmlen @@ eval_tm (V.Env.extend_tm clo.env var) clo.body *\) *)
(* (\*     in { clo with body } *\) *)

(* (\** Recurse down a dimension. *\) *)
(* and do_dim_rec (mot : V.tp) (zero : V.tm) (succ : V.tm) (scrut : V.tm) : V.tm = *)
(*   match scrut with *)
(*   | V.DimZero -> *)
(*     zero *)
(*   | V.DimSucc d -> *)
(*     do_insts succ [Lazy.from_val d; Lazy.from_fun @@ fun () -> do_dim_rec mot zero succ d] *)
(*   | V.Neu neu -> *)
(*     V.Neu (V.Neu.push neu (V.DimRec { mot; zero; succ })) *)
(*   | _ -> *)
(*     failwith "bad do_dim_rec" *)

(* and do_tp_inst (tp : V.tp) (arg : V.tp) : V.tp = *)
(*   __ *)

(* (\** Decode a shape to a type. *\) *)
(* and do_el_shape (v : V.tm) : V.tp = *)
(*   match v with *)
(*   | V.Compound tele -> V.Record (do_tele_el_shape tele) *)
(*   | V.Neu neu -> V.ElShape neu *)
(*   | _ -> failwith "bad do_el_shape" *)

(* (\** Decode a telescope of shapes to a telescope of types. *\) *)
(* and do_tele_el_shape (tele : (S.tm, V.tm) V.tele) : (S.tp, V.tp) V.tele = *)
(*   match tele with *)
(*   | Nil -> Nil *)
(*   | Cons (v, clo) -> Cons (do_el_shape v, { clo with body = List.map (fun tm -> S.ElShape tm) clo.body }) *)

(** Construct a term out of a splice. *)
and splice_tm (splice : S.tm Splice.m) : V.tm =
  let tm, env = Splice.run V.Env.empty splice in
  eval_tm env tm

(** Construct a meta-abstracted term out of a splice. *)
and splice_meta_tm (splice : S.meta_tm Splice.m) : V.meta_tm =
  let tm, env = Splice.run V.Env.empty splice in
  eval_meta_tm env tm

(* (\** Construct a type out of a splice. *\) *)
(* and splice_tp (splice : S.tp Splice.m) : V.tp = *)
(*   let tp, env = Splice.run V.Env.empty splice in *)
(*   eval_tp env tp *)

(* (\** {0} Quotation *\) *)

(* (\* TODO: Eta expansion *\) *)
(* and quote_tm (lvl : Lvl.t) (v : V.tm) : S.tm = *)
(*   match v with *)
(*   | V.Neu neu -> *)
(*     quote_neu lvl neu *)
(*   | V.DimZero -> *)
(*     S.DimZero *)
(*   | V.DimSucc v -> *)
(*     S.DimSucc (quote_tm lvl v) *)
(*   | V.Tuple vs -> *)
(*     S.Tuple (List.map (fun v -> quote_tm lvl (Lazy.force v)) vs) *)
(*   | V.Pt -> *)
(*     S.Pt *)
(*   | V.Compound tele -> *)
(*     Debug.print "Quoting compound: %a" SExpr.dump (SExpr.list @@ V.tm_tele_sexpr tele); *)
(*     S.Compound (quote_tm_tele lvl tele) *)
(*   | V.MetaAbs clo -> *)
(*     S.MetaAbs (quote_tm_clo lvl 1 clo) *)


(* and quote_tp (lvl : Lvl.t) (tp : V.tp) : S.tp = *)
(*   match tp with *)
(*   | V.Dim -> *)
(*     S.Dim *)
(*   | V.Record tele -> *)
(*     S.Record (quote_tp_tele lvl tele) *)
(*   | V.TpMetaAbs (base, fam) -> *)
(*     S.TpMetaAbs (quote_tp lvl base, quote_tp_clo lvl 1 fam) *)
(*   | V.ShapeUniv v -> *)
(*     S.ShapeUniv (quote_tm lvl v) *)
(*   | V.ElShape neu -> *)
(*     S.ElShape (quote_neu lvl neu) *)
(*   | V.PointUniv v -> *)
(*     S.PointUniv (quote_tm lvl v) *)
(*   | V.ElPoint neu -> *)
(*     S.ElShape (quote_neu lvl neu) *)

(* and quote_hd (lvl : Lvl.t) (hd : V.hd) : S.tm = *)
(*   S.Var (lvl - hd - 1) *)

(* and quote_frm (lvl : Lvl.t) (frm : V.frm) (tm : S.tm) : S.tm = *)
(*   match frm with *)
(*   | V.Proj ix -> *)
(*     S.Proj (tm, ix) *)
(*   | V.Inst arg -> *)
(*     S.Inst (tm, quote_tm lvl (Lazy.force arg)) *)
(*   | V.Digit d -> *)
(*     S.Digit (d, tm) *)
(*   | V.DimRec {mot; zero; succ} -> *)
(*     let mot = quote_tp lvl mot *)
(*     and zero = quote_tm lvl zero *)
(*     and succ = quote_tm lvl succ *)
(*     in S.DimRec { mot; zero; succ; scrut = tm } *)

(* and quote_neu (lvl : Lvl.t) (neu : V.neu) : S.tm = *)
(*   List.fold_right (quote_frm lvl) neu.spine (quote_hd lvl neu.hd) *)

(* and quote_tm_clo (lvl : Lvl.t) (n : int) (clo : S.tm V.clo) = *)
(*   let vars = List.init n (fun n -> Lazy.from_val @@ V.var (lvl + n)) *)
(*   in quote_tm (lvl + n) (eval_tm (V.Env.extend_tms clo.env vars) clo.body) *)

(* and quote_tp_clo (lvl : Lvl.t) (n : int) (clo : S.tp V.clo) = *)
(*   let vars = List.init n (fun n -> Lazy.from_val @@ V.var (lvl + n)) *)
(*   in quote_tp (lvl + n) (eval_tp (V.Env.extend_tms clo.env vars) clo.body) *)

(* and quote_tm_tele (lvl : Lvl.t) (tele : (S.tm, V.tm) V.tele) : S.tm list = *)
(*   match tele with *)
(*   | Nil -> [] *)
(*   | Cons (v, tele_clo) -> *)
(*     let tm = quote_tm lvl v *)
(*     and tele = *)
(*       quote_tm_tele (lvl + 1) @@ *)
(*       eval_tm_tele (V.Env.extend_tm tele_clo.env (Lazy.from_val @@ V.var lvl)) tele_clo.body *)
(*     in tm :: tele *)

(* and quote_tp_tele (lvl : Lvl.t) (tele : (S.tp, V.tp) V.tele) : S.tp list = *)
(*   match tele with *)
(*   | Nil -> [] *)
(*   | Cons (v, tele_clo) -> *)
(*     let tp = quote_tp lvl v *)
(*     and tele = *)
(*       quote_tp_tele (lvl + 1) @@ *)
(*       eval_tp_tele (V.Env.extend_tm tele_clo.env (Lazy.from_val @@ V.var lvl)) tele_clo.body *)
(*     in tp :: tele *)
