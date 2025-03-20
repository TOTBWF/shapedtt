open Data

include Syntax
module Idx = Idx

let rec tm_sexpr (tm : S.tm) : SExpr.t =
  match tm with
  | Var x ->
     SExpr.fn "var" [SExpr.int x]
  | DimZero ->
    SExpr.atom "dim-zero"
  | DimSucc tm ->
    SExpr.fn "dim-succ" [tm_sexpr tm]
  | Tuple tms ->
    SExpr.fn "tuple" (List.map tm_sexpr tms)
  | Proj (tm, i) ->
    SExpr.fn "proj" [tm_sexpr tm; SExpr.int i]
  | Pt ->
    SExpr.atom "pt"
  | Compound tms ->
    SExpr.fn "compound" (List.map tm_sexpr tms)
  | MetaAbs tm ->
    SExpr.fn "meta-abs" [tm_sexpr tm]
  | Inst (tm, tms) ->
    SExpr.fn "inst" (tm_sexpr tm :: List.map tm_sexpr tms)
  | Digit (d, tm) ->
    SExpr.fn "digit" [SExpr.bool d; tm_sexpr tm]
  | DimRec {mot; zero; succ; scrut} ->
    SExpr.fn "dim-rec" [tp_sexpr mot; tm_sexpr zero; tm_sexpr succ; tm_sexpr scrut]

and tp_sexpr (tp : S.tp) : SExpr.t = SExpr.atom "todo"
