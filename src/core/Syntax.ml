open Data

include Syntax
module Idx = Idx

(** Dump a term to debug S-expressions. *)
let rec debug_tm_sexpr (tm : S.tm) : SExpr.t =
  match tm with
  | Var x ->
    SExpr.fn "var" [SExpr.int x]
  | DimZero ->
    SExpr.atom "dim-zero"
  | DimSucc tm ->
    SExpr.fn "dim-succ" [debug_tm_sexpr tm]
  | Lam body ->
    SExpr.fn "lam" [debug_tm_sexpr body]
  | App (tm, arg) ->
    SExpr.fn "app" [debug_tm_sexpr tm; debug_tm_sexpr arg]
  | Tuple tms ->
    SExpr.fn "tuple" (List.map debug_tm_sexpr tms)
  | Proj (tm, ix) ->
    SExpr.fn "proj" [debug_tm_sexpr tm; SExpr.int ix]
  | Pt ->
    SExpr.atom "pt"
  | Compound tms ->
    SExpr.fn "compound" (List.map debug_tm_sexpr tms)
  | AppZero tm ->
    SExpr.fn "app-zero" [debug_tm_sexpr tm]
  | Inst (mtm, tm) ->
    SExpr.fn "inst" [debug_meta_tm_sexpr mtm; debug_tm_sexpr tm]
  | DimRec {mot; zero; succ; scrut} ->
    SExpr.fn "dim-rec" [debug_tp_sexpr mot; debug_tm_sexpr zero; debug_tm_sexpr succ; debug_tm_sexpr scrut]

(** Dump a meta-abstracted term to debug S-expressions. *)
and debug_meta_tm_sexpr (tm : S.meta_tm) : SExpr.t =
  match tm with
  | MetaAbs tm ->
    SExpr.fn "meta-abs" [debug_tm_sexpr tm]
  | AppOne tm ->
    SExpr.fn "app-one" [debug_tm_sexpr tm]
  | MetaAppZero mtm ->
    SExpr.fn "meta-app-zero" [debug_meta_tm_sexpr mtm]
  | MetaAppOne mtm ->
    SExpr.fn "meta-app-one" [debug_meta_tm_sexpr mtm]

(** Dump a type to debug S-expressions. *)
and debug_tp_sexpr (tp : S.tp) : SExpr.t =
  match tp with
  | TpVar ix ->
    SExpr.fn "tp-var" [SExpr.int ix]
  | Dim ->
    SExpr.atom "dim"
  | Pi (base, fam) ->
    SExpr.fn "pi" [debug_tp_sexpr base; debug_tp_sexpr fam]
  | Record tele ->
    SExpr.fn "record" (List.map debug_tp_sexpr tele)
  | TpInst (mtp, tm) ->
    SExpr.fn "tp-inst" [debug_meta_tp_sexpr mtp; debug_tm_sexpr tm]
  | ShapeUniv tm ->
    SExpr.fn "shape-univ" [debug_tm_sexpr tm]
  | ElShape tm ->
    SExpr.fn "el-shape" [debug_tm_sexpr tm]
  | PointUniv tm ->
    SExpr.fn "point-univ" [debug_tm_sexpr tm]
  | ElPoint tm ->
    SExpr.fn "el-point" [debug_tm_sexpr tm]

(** Dump a meta-abstracted type to debug S-expressions. *)
and debug_meta_tp_sexpr (mtp : S.meta_tp) : SExpr.t =
  match mtp with
  | TpMetaAbs tp ->
    SExpr.fn "tp-meta-abs" [debug_tp_sexpr tp]

let dump_tm (fmt : Format.formatter) (tm : S.tm) : unit =
  SExpr.pp_print_sexpr fmt (debug_tm_sexpr tm)

let dump_meta_tm (fmt : Format.formatter) (mtm : S.meta_tm) : unit =
  SExpr.pp_print_sexpr fmt (debug_meta_tm_sexpr mtm)

let dump_tp (fmt : Format.formatter) (tp : S.tp) : unit =
  SExpr.pp_print_sexpr fmt (debug_tp_sexpr tp)

let dump_meta_tp (fmt : Format.formatter) (mtp : S.meta_tp) : unit =
  SExpr.pp_print_sexpr fmt (debug_meta_tp_sexpr mtp)
