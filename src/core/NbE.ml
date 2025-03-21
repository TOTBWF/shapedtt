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
    (* TODO: Should this push the zero application down into the spine? *)
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
    (* TODO: Should this push the one application down into the spine? *)
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

(** Construct a term out of a splice. *)
and splice_tm (splice : S.tm Splice.m) : V.tm =
  let tm, env = Splice.run V.Env.empty splice in
  eval_tm env tm

(** Construct a meta-abstracted term out of a splice. *)
and splice_meta_tm (splice : S.meta_tm Splice.m) : V.meta_tm =
  let tm, env = Splice.run V.Env.empty splice in
  eval_meta_tm env tm

(** Construct a type out of a splice. *)
and splice_tp (splice : S.tp Splice.m) : V.tp =
  let tp, env = Splice.run V.Env.empty splice in
  eval_tp env tp

(** {0} Quotation *)

(* TODO: Eta expansion *)
and quote_tm (lvl : Lvl.t) (v : V.tm) : S.tm =
  match v with
  | V.Neu neu ->
    quote_neu lvl neu
  | V.DimZero ->
    S.DimZero
  | V.DimSucc v ->
    S.DimSucc (quote_tm lvl v)
  | V.Lam clo ->
    S.Lam (quote_tm_clo clo)
  | V.Tuple vs ->
    S.Tuple (List.map (fun v -> quote_tm lvl (Lazy.force v)) vs)
  | V.Compound tele ->
    S.Compound (quote_tm_tele tele)


and quote_tp (lvl : Lvl.t) (tp : V.tp) : S.tp =
  match tp with
  | V.Dim ->
    S.Dim
  | V.Pi (base, clo) ->
    S.Pi (quote_tp lvl base, quote_tp_clo clo)
  | V.Record tele ->
    S.Record (quote_tp_tele tele)
  | V.ShapeUniv v ->
    S.ShapeUniv (quote_tm lvl v)
  | V.ElShape neu ->
    S.ElShape (quote_neu lvl neu)
  | V.PointUniv v ->
    S.PointUniv (quote_tm lvl v)
  | V.ElPoint neu ->
    S.ElShape (quote_neu lvl neu)

and quote_neu (lvl : Lvl.t) (neu : V.neu) : S.tm =
  (* TODO: Is this the right way to handle zeros? *)
  let rec app_zeros n tm =
    if n <= 0 then
      tm
    else S.AppZero (app_zeros (n - 1) tm)
  in
  List.fold_right (quote_frm lvl) neu.spine (app_zeros neu.zeros (quote_hd lvl neu.hd))

and quote_hd (lvl : Lvl.t) (hd : V.hd) : S.tm =
  match hd with
  | V.Var x ->
    S.Var (lvl - x - 1)
  | V.Pt ->
    S.Pt
  | V.Inst (mneu, tm) ->
    S.Inst (quote_meta_neu lvl mneu, quote_tm lvl (Lazy.force tm))

and quote_frm (lvl : Lvl.t) (frm : V.frm) (tm : S.tm) : S.tm =
  match frm with
  | V.App arg ->
    S.App (tm, quote_tm lvl (Lazy.force arg))
  | V.Proj ix ->
    S.Proj (tm, ix)
  | V.DimRec {mot; zero; succ} ->
    let mot = quote_tp lvl mot
    and zero = quote_tm lvl zero
    and succ = quote_tm lvl succ
    in S.DimRec { mot; zero; succ; scrut = tm }

and quote_meta_neu (lvl : Lvl.t) (mneu : V.meta_neu) : S.meta_tm =
  List.fold_right (quote_meta_frm lvl) mneu.meta_spine (quote_meta_hd lvl mneu.meta_hd)

and quote_meta_hd (lvl : Lvl.t) (mhd : V.meta_hd) : S.meta_tm =
  match mhd with
  | V.AppOne neu ->
    S.AppOne (quote_neu lvl neu)

and quote_meta_frm (_lvl : Lvl.t) (mfrm : V.meta_frm) (tm : S.meta_tm) : S.meta_tm =
  match mfrm with
  | V.MetaAppZero -> S.MetaAppZero tm
  | V.MetaAppOne -> S.MetaAppOne tm

and quote_tm_clo (clo : S.tm V.clo) : S.tm =
  let var = Lazy.from_val (V.var clo.env.tmlen) in
  quote_tm clo.env.tmlen (eval_tm (V.Env.extend_tm clo.env var) clo.body)

and quote_tp_clo (clo : S.tp V.clo) : S.tp =
  let var = Lazy.from_val (V.var clo.env.tmlen) in
  quote_tp clo.env.tmlen (eval_tp (V.Env.extend_tm clo.env var) clo.body)

and quote_tm_tele (tele : S.tm List.t V.clo) : S.tm list =
  let rec go (env : V.env) =
    function
    | [] ->
      []
    | tm :: tms ->
      let tm = quote_tm env.tmlen (eval_tm env tm)
      and tms = go (V.Env.extend_tm env (Lazy.from_val (V.var env.tmlen))) tms
      in tm :: tms
  in go tele.env tele.body

and quote_tp_tele (tele : S.tp List.t V.clo) : S.tp list =
  let rec go (env : V.env) =
    function
    | [] ->
      []
    | tm :: tms ->
      let tm = quote_tp env.tmlen (eval_tp env tm)
      and tms = go (V.Env.extend_tm env (Lazy.from_val (V.var env.tmlen))) tms
      in tm :: tms
 in go tele.env tele.body

  (* match tele.body with *)
  (* | [] -> [] *)
  (* | (tm :: tms) -> *)
  (*   let tm = quote_tm lvl (eval_) *)

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
