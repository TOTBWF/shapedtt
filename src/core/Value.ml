module S = Syntax
module V = Data.Value

include V

module Lvl = Data.Lvl

let var (lvl : Lvl.t) : V.tm =
  Neu { hd = lvl; spine = [] }

module Tele =
struct
  type ('s, 'v) t = ('s, 'v) V.tele

  let length (tele : ('s, 'v) tele) : int =
    match tele with
    | Nil -> 0
    | Cons (_, tele_clo) -> 1 + List.length tele_clo.body
end

module Env =
struct
  type t = V.env

  let extend_tm (env : t) (v : tm Lazy.t) : t =
    { env with tms = v :: env.tms; tmlen = env.tmlen + 1 }

  let extend_tms (env : t) (vs : tm Lazy.t List.t) : t =
    { env with tms = List.rev vs @ env.tms; tmlen = env.tmlen + List.length vs }

  let extend_tp (env : t) (tp : tp Lazy.t) : t =
    { env with tps =  tp :: env.tps; tplen = env.tplen + 1 }

  let nth_tm (env : t) (ix : S.Idx.t) : V.tm Lazy.t =
    List.nth env.tms ix

  let nth_tp (env : t) (ix : S.Idx.t) : V.tp Lazy.t =
    List.nth env.tps ix

  let empty : t =
    { tms = []; tmlen = 0; tps = []; tplen = 0 }

  let append (env1 : t) (env2 : t) : t =
    {
      tms = env1.tms @ env2.tms;
      tmlen = env1.tmlen + env2.tmlen;
      tps = env1.tps @ env2.tps;
      tplen = env1.tmlen + env2.tmlen;
    }
end

module Neu =
struct
  let push (neu : neu) (frame : frm) : neu =
    { neu with spine = frame :: neu.spine }
end

let rec tm_sexpr (v : V.tm) : SExpr.t =
  match v with
  | Neu neu ->
    SExpr.fn "neu" (hd_sexpr neu.hd :: List.map frm_sexpr (List.rev neu.spine))
  | DimZero ->
    SExpr.atom "dim-zero"
  | DimSucc v ->
    SExpr.fn "dim-succ" [tm_sexpr v]
  | Tuple vs ->
    SExpr.fn "tuple" (List.map (fun v -> tm_sexpr (Lazy.force v)) vs)
  | Pt ->
    SExpr.atom "pt"
  | Compound vs ->
    SExpr.fn "compound" (tm_tele_sexpr vs)
  | MetaAbs (n, clo) ->
    SExpr.fn "meta-abs" [SExpr.int n; clo_sexpr S.tm_sexpr clo]

and tp_sexpr (tp : V.tp) : SExpr.t = SExpr.atom "todo"

and hd_sexpr (hd : V.hd) : SExpr.t = SExpr.fn "var" [SExpr.int hd]

and frm_sexpr (frm : V.frm) : SExpr.t =
  match frm with
  | Proj i ->
    SExpr.fn "proj" [SExpr.int i]
  | Inst vs ->
    SExpr.fn "inst" (List.map (fun v -> tm_sexpr (Lazy.force v)) vs)
  | Digit d ->
    SExpr.fn "digit" [SExpr.bool d]
  | DimRec {mot; zero; succ} ->
    SExpr.fn "dim-rec" [tp_sexpr mot; tm_sexpr zero; tm_sexpr succ]

and tm_tele_sexpr (tele : (S.tm, V.tm) tele) : SExpr.t list =
  match tele with
  | Nil -> []
  | Cons (v, tms) -> [tm_sexpr v; clo_sexpr (fun tms -> SExpr.list (List.map S.tm_sexpr tms)) tms]

and clo_sexpr : 'a. ('a -> SExpr.t) -> 'a clo -> SExpr.t =
  fun body_sexpr clo ->
  SExpr.fn "clo" [env_sexpr clo.env; body_sexpr clo.body]

and env_sexpr (env : Env.t) : SExpr.t =
  SExpr.list (List.map (fun v -> tm_sexpr (Lazy.force v)) env.tms)
