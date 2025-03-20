(** {0} Evaluation *)
module Idx = Data.Idx

module S = Syntax
module V = Value

(** Evaluate a term. *)
let rec eval_tm (env : V.env) (tm : S.tm) : V.tm =
  match tm with
  | S.Var ix ->
    Lazy.force (V.Env.nth_tm env ix)
  | S.DimZero ->
    V.DimZero
  | S.DimSucc tm ->
    V.DimSucc (eval_tm env tm)
  | S.Tuple tms ->
    V.Tuple (List.map (eval_tm_lazy env) tms)
  | S.Proj (tm, ix) ->
    do_proj (eval_tm env tm) ix
  | S.Pt ->
    V.Pt
  | S.Compound tms ->
    V.Compound (eval_tm_tele env tms)
  | S.MetaAbs tm -> V.MetaAbs {body = tm; env}
  | S.Inst (tm, tms) ->
    do_inst (eval_tm env tm) (List.map (eval_tm_lazy env) tms)
  | S.Digit (d, tm) ->
    do_digit d (eval_tm env tm)
  | S.DimRec elim ->
    do_dim_rec (eval_tp env elim.mot) (eval_tm env elim.zero) (eval_tm env elim.succ) (eval_tm env elim.scrut)

(** Evaluate a type. *)
and eval_tp (env : V.env) (tp : S.tp) : V.tp =
  match tp with
  | S.TpVar ix ->
    Lazy.force (V.Env.nth_tp env ix)
  | S.Dim ->
    V.Dim
  | S.Record tele ->
    V.Record (eval_tp_tele env tele)
  | S.TpMetaAbs (tele, tp) ->
    V.MetaAbs (eval_tp_tele env tele, { body = tp; env })
  | S.ShapeUniv dim ->
    V.ShapeUniv (eval_tm env dim)
  | S.ElShape tm ->
    do_el_shape (eval_tm env tm)
  | S.PointUniv dim ->
    V.PointUniv (eval_tm env dim)
  | S.ElPoint _ -> failwith "el point not implemented"

(** Lazily evaluate a term. *)
and eval_tm_lazy (env : V.env) (tm : S.tm) : V.tm Lazy.t =
  Lazy.from_fun @@ fun () -> eval_tm env tm

(** Evaluate a telescope of terms. *)
and eval_tm_tele (env : V.env) (tms : S.tm List.t) : (S.tm, V.tm) V.tele =
  match tms with
  | [] -> Nil
  | (tm :: tms) -> Cons (eval_tm env tm, { body = tms; env })

(** Evaluate a telescope of types. *)
and eval_tp_tele (env : V.env) (tms : S.tp List.t) : (S.tp, V.tp) V.tele =
  match tms with
  | [] -> Nil
  | (tp :: tps) -> Cons (eval_tp env tp, { body = tps; env })

(** Project the nth field out of a tuple. *)
and do_proj (v : V.tm) (ix : Idx.t) : V.tm =
  match v with
  | V.Tuple vs -> Lazy.force (List.nth vs ix)
  | V.Neu neu -> V.Neu (V.Neu.push neu (V.Proj ix))
  | _ -> failwith "bad do_proj"

(** Instantiate a term-level meta-abstraction. *)
and do_inst (v : V.tm) (vs : V.tm Lazy.t List.t) : V.tm =
  match v with
  | V.MetaAbs clo -> eval_tm (V.Env.extend_tms clo.env vs) clo.body
  | V.Neu neu -> V.Neu (V.Neu.push neu (V.Inst vs))
  | _ -> failwith "bad do_inst"

(** Apply a digit to a shape. *)
and do_digit (d : bool) (v : V.tm) : V.tm =
  match v with
  | V.Compound vs -> V.Compound (do_tele_digit d vs)
  | V.Neu neu -> V.Neu (V.Neu.push neu (Digit d))
  | _ -> failwith "bad do_digit"

(** Apply a digit to a telescope of shapes. *)
and do_tele_digit (d : bool) (tele : (S.tm, V.tm) V.tele) : (S.tm, V.tm) V.tele =
  match tele with
  | Nil -> Nil
  | Cons (v, clo) -> Cons (do_digit d v, { clo with body = List.map (fun tm -> S.Digit (d, tm)) clo.body })

(** Recurse down a dimension. *)
and do_dim_rec (mot : V.tp) (zero : V.tm) (succ : V.tm) (scrut : V.tm) : V.tm =
  match scrut with
  | V.DimZero -> zero
  | V.DimSucc d -> do_inst succ [Lazy.from_val d; Lazy.from_fun @@ fun () -> do_dim_rec mot zero succ d]
  | V.Neu neu -> V.Neu (V.Neu.push neu (V.DimRec { mot; zero; succ }))
  | _ -> failwith "bad do_dim_rec"

(** Decode a shape to a type. *)
and do_el_shape (v : V.tm) : V.tp =
  match v with
  | V.Compound tele -> V.Record (do_tele_el_shape tele)
  | V.Neu neu -> V.ElShape neu
  | _ -> failwith "bad do_el_shape"

(** Decode a telescope of shapes to a telescope of types. *)
and do_tele_el_shape (tele : (S.tm, V.tm) V.tele) : (S.tp, V.tp) V.tele =
  match tele with
  | Nil -> Nil
  | Cons (v, clo) -> Cons (do_el_shape v, { clo with body = List.map (fun tm -> S.ElShape tm) clo.body })
