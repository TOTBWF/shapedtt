(** {0} Quotation *)

module S = Syntax
module V = Value

module Lvl = V.Lvl

(* TODO: Eta expansion *)
let rec quote_tm (lvl : Lvl.t) (v : V.tm) : S.tm =
  match v with
  | V.Neu neu ->
    quote_neu lvl neu
  | V.DimZero ->
    S.DimZero
  | V.DimSucc v ->
    S.DimSucc (quote_tm lvl v)
  | V.Tuple vs ->
    S.Tuple (List.map (fun v -> quote_tm lvl (Lazy.force v)) vs)
  | V.Pt ->
    S.Pt
  | V.Compound tele ->
    S.Compound (quote_tm_tele lvl tele)
  | V.MetaAbs clo ->
    S.MetaAbs (quote_tm_clo lvl 1 clo)


and quote_tp (lvl : Lvl.t) (tp : V.tp) : S.tp =
  match tp with
  | V.Dim ->
    S.Dim
  | V.Record tele ->
    S.Record (quote_tp_tele lvl tele)
  | V.TpMetaAbs (base, fam) ->
    S.TpMetaAbs (quote_tp lvl base, quote_tp_clo lvl 1 fam)
  | V.ShapeUniv v ->
    S.ShapeUniv (quote_tm lvl v)
  | V.ElShape neu ->
    S.ElShape (quote_neu lvl neu)
  | V.PointUniv v ->
    S.PointUniv (quote_tm lvl v)
  | V.ElPoint neu ->
    S.ElShape (quote_neu lvl neu)

and quote_hd (lvl : Lvl.t) (hd : V.hd) : S.tm =
  S.Var (lvl - hd - 1)

and quote_frm (lvl : Lvl.t) (frm : V.frm) (tm : S.tm) : S.tm =
  match frm with
  | V.Proj ix ->
    S.Proj (tm, ix)
  | V.Inst arg ->
    S.Inst (tm, quote_tm lvl (Lazy.force arg))
  | V.Digit d ->
    S.Digit (d, tm)
  | V.DimRec {mot; zero; succ} ->
    let mot = quote_tp lvl mot
    and zero = quote_tm lvl zero
    and succ = quote_tm lvl succ
    in S.DimRec { mot; zero; succ; scrut = tm }

and quote_neu (lvl : Lvl.t) (neu : V.neu) : S.tm =
  List.fold_right (quote_frm lvl) neu.spine (quote_hd lvl neu.hd)

and quote_tm_clo (lvl : Lvl.t) (n : int) (clo : S.tm V.clo) =
  let vars = List.init n (fun n -> Lazy.from_val @@ V.var (lvl + n))
  in quote_tm (lvl + n) (Eval.eval_tm (V.Env.extend_tms clo.env vars) clo.body)

and quote_tp_clo (lvl : Lvl.t) (n : int) (clo : S.tp V.clo) =
  let vars = List.init n (fun n -> Lazy.from_val @@ V.var (lvl + n))
  in quote_tp (lvl + n) (Eval.eval_tp (V.Env.extend_tms clo.env vars) clo.body)

and quote_tm_tele (lvl : Lvl.t) (tele : (S.tm, V.tm) V.tele) : S.tm list =
  match tele with
  | Nil -> []
  | Cons (v, tele_clo) ->
    let tm = quote_tm lvl v
    and tele =
      quote_tm_tele (lvl + 1) @@
      Eval.eval_tm_tele (V.Env.extend_tm tele_clo.env (Lazy.from_val @@ V.var lvl)) tele_clo.body
    in tm :: tele

and quote_tp_tele (lvl : Lvl.t) (tele : (S.tp, V.tp) V.tele) : S.tp list =
  match tele with
  | Nil -> []
  | Cons (v, tele_clo) ->
    let tp = quote_tp lvl v
    and tele =
      quote_tp_tele (lvl + 1) @@
      Eval.eval_tp_tele (V.Env.extend_tm tele_clo.env (Lazy.from_val @@ V.var lvl)) tele_clo.body
    in tp :: tele
