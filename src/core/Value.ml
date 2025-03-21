module S = Syntax
module V = Data.Value

include V

module Lvl = Data.Lvl

let var (lvl : Lvl.t) : V.tm =
  Neu { hd = Var lvl; spine = []; zeros = 0 }

let pt : V.tm =
  Neu { hd = Pt; spine = []; zeros = 0 }

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

module MetaNeu =
struct
  let push (neu : meta_neu) (frame : meta_frm) : meta_neu =
    { neu with meta_spine = frame :: neu.meta_spine }
end

let rec debug_tm_sexpr (v : V.tm) : SExpr.t =
  match v with
  | Neu neu ->
    SExpr.fn "neu" (debug_neu_sexpr neu)
  | DimZero ->
    SExpr.atom "dim-zero"
  | DimSucc v ->
    SExpr.fn "dim-succ" [debug_tm_sexpr v]
  | Lam clo ->
    SExpr.fn "lam" [debug_clo_sexpr S.debug_tm_sexpr clo]
  | Tuple vs ->
    SExpr.fn "tuple" (List.map (fun v -> debug_tm_sexpr (Lazy.force v)) vs)
  | Compound clo ->
    SExpr.fn "tuple" [debug_clo_sexpr (fun tms -> SExpr.list (List.map S.debug_tm_sexpr tms)) clo]

and debug_meta_tm_sexpr (mv : V.meta_tm) : SExpr.t =
  match mv with
  | MetaNeu mneu ->
    SExpr.fn "meta-neu" (debug_meta_neu_sexpr mneu)
  | MetaAbs clo ->
    SExpr.fn "meta-abs" [debug_clo_sexpr S.debug_tm_sexpr clo]

and debug_tp_sexpr (tp : V.tp) : SExpr.t =
  match tp with
  | Dim ->
    SExpr.atom "dim"
  | Pi (base, clo) ->
    SExpr.fn "pi" [debug_tp_sexpr base; debug_clo_sexpr S.debug_tp_sexpr clo]
  | Record tele ->
    SExpr.fn "record" [debug_clo_sexpr (fun tps -> SExpr.list (List.map S.debug_tp_sexpr tps)) tele]
  | ShapeUniv tm ->
    SExpr.fn "shape-univ" [debug_tm_sexpr tm]
  | ElShape neu ->
    SExpr.fn "el-shape" (debug_neu_sexpr neu)
  | PointUniv tm ->
    SExpr.fn "point-univ" [debug_tm_sexpr tm]
  | ElPoint neu ->
    SExpr.fn "el-point" (debug_neu_sexpr neu)

and debug_meta_tp_sexpr (mtp : V.meta_tp) : SExpr.t =
  match mtp with
  | TpMetaAbs clo ->
    SExpr.fn "tp-meta-abs" [debug_clo_sexpr S.debug_tp_sexpr clo]

and debug_neu_sexpr (neu : V.neu) : SExpr.t List.t =
  debug_hd_sexpr neu.hd :: List.rev_map debug_frm_sexpr neu.spine

and debug_hd_sexpr (hd : V.hd) : SExpr.t =
  match hd with
  | Var lvl ->
    SExpr.fn "var" [SExpr.int lvl]
  | Pt ->
    SExpr.atom "pt"
  | Inst (mtm, tm) ->
    SExpr.fn "inst" [SExpr.list (debug_meta_neu_sexpr mtm); debug_tm_sexpr (Lazy.force tm)]

and debug_frm_sexpr (frm : V.frm) : SExpr.t =
  match frm with
  | App tm ->
    SExpr.fn "app" [debug_tm_sexpr (Lazy.force tm)]
  | Proj ix ->
    SExpr.fn "proj" [SExpr.int ix]
  | DimRec {mot; zero; succ} ->
    SExpr.fn "dim-rec" [debug_tp_sexpr mot; debug_tm_sexpr zero; debug_tm_sexpr succ]


and debug_meta_neu_sexpr (mneu : V.meta_neu) : SExpr.t List.t =
  debug_meta_hd_sexpr mneu.meta_hd :: List.rev_map debug_meta_frm_sexpr mneu.meta_spine

and debug_meta_hd_sexpr (mhd : V.meta_hd) : SExpr.t =
  match mhd with
  | AppOne neu ->
    SExpr.fn "app-one" (debug_neu_sexpr neu)

and debug_meta_frm_sexpr (mfrm : V.meta_frm) : SExpr.t =
  match mfrm with
  | MetaAppZero ->
    SExpr.atom "meta-app-zero"
  | MetaAppOne ->
    SExpr.atom "meta-app-one"

and debug_clo_sexpr : 'a. ('a -> SExpr.t) -> 'a clo -> SExpr.t =
  fun body_sexpr clo ->
  SExpr.fn "clo" [debug_env_sexpr clo.env; body_sexpr clo.body]

and debug_env_sexpr (env : Env.t) : SExpr.t =
  SExpr.list (List.rev_map (fun v -> debug_tm_sexpr (Lazy.force v)) env.tms)

let dump_tm (fmt : Format.formatter) (tm : V.tm) : unit =
  SExpr.pp_print_sexpr fmt (debug_tm_sexpr tm)

let dump_meta_tm (fmt : Format.formatter) (mtm : V.meta_tm) : unit =
  SExpr.pp_print_sexpr fmt (debug_meta_tm_sexpr mtm)

let dump_tp (fmt : Format.formatter) (tp : V.tp) : unit =
  SExpr.pp_print_sexpr fmt (debug_tp_sexpr tp)

let dump_meta_tp (fmt : Format.formatter) (mtp : V.meta_tp) : unit =
  SExpr.pp_print_sexpr fmt (debug_meta_tp_sexpr mtp)
