(** Terms constructed relative to an arbitrary environment. *)

open Data

module S = Syntax
module V = Value

type env = { tplen : int; tmlen : int }

type 'a m = env -> 'a

let var (lvl : Lvl.t) : S.tm m =
  fun env -> S.Var (env.tmlen - lvl - 1)

let tpvar (lvl : Lvl.t) : S.tp m =
  fun env -> S.TpVar (env.tplen - lvl - 1)

let (let+) (a : 'a m) (f : 'a -> 'b) : 'b m =
  fun env -> f (a env)

let (and+) (a : 'a m) (b : 'b m) : ('a * 'b) m =
  fun env -> (a env, b env)

let many (xs : 'a m list) : 'a list m =
  fun env -> List.map (fun x -> x env) xs

let pure (x : 'a) : 'a m =
  fun _ -> x

let run ~tplen ~tmlen (tb : 'a m) : 'a =
  tb { tplen; tmlen }

let with_var (k : S.tm m -> 'a m) : 'a m =
  fun env -> k (var env.tmlen) { env with tmlen = env.tmlen + 1 }

type ('tp, 'tm, 'r) tele =
  | Nil of 'r m
  | Cons of 'tp m * ('tm m -> ('tp, 'tm, 'r) tele)

let nil (r : 'r m) : ('tp, 'tm, 'r) tele =
  Nil r

let cons (tp : 'tp m) (k : 'tm m -> ('tp, 'tm, 'r) tele) : ('tp, 'tm, 'r) tele =
  Cons (tp, k)

let rec telescope (tele : ('tp, S.tm, 'r) tele) : ('tp list * 'r) m =
  match tele with
  | Nil r ->
    let+ r = r
    in [], r
  | Cons (x, k) ->
    let+ x = x
    and+ xs, r = with_var (fun x -> telescope (k x))
    in x :: xs, r

(** {0} Higher-Order Abstract Syntax interface for environment-relative terms. *)

let dim_zero : S.tm m =
  pure S.DimZero

let dim_succ (dm : S.tm m) : S.tm m =
  let+ d = dm in
  S.DimSucc d

let rec dim_lit (n : int) : S.tm m =
  if n <= 0 then
    dim_zero
  else dim_succ (dim_lit (n - 1))

let tuple (tms : S.tm m list) : S.tm m =
  let+ tms = many tms in
  S.Tuple tms

let proj (tm : S.tm m) (ix : Idx.t) : S.tm m =
  let+ tm = tm in
  S.Proj (tm, ix)

let pt : S.tm m =
  pure S.Pt

let compound (tele : (S.tm, S.tm, unit) tele) : S.tm m =
  let+ tms, _ = telescope tele in
  S.Compound tms

let meta_abs (tele : (unit, S.tm, S.tm) tele) : S.tm m =
  let+ (_, tm) = telescope tele
  in S.MetaAbs tm

let inst (tm : S.tm m) (tms : S.tm m list) : S.tm m =
  let+ tm = tm
  and+ tms = many tms
  in S.Inst (tm, tms)

let digit (d : bool) (tm : S.tm m) : S.tm m =
  let+ tm = tm
  in S.Digit (d, tm)

let dim_rec (mot : S.tm m -> S.tp m) (zero : S.tm m) (succ : S.tm m) (scrut : S.tm m) =
  let+ mot = with_var mot
  and+ zero = zero
  and+ succ = succ
  and+ scrut = scrut
  in S.DimRec { mot; zero; succ; scrut }

let dim : S.tp m =
  pure S.Dim

let record (tele : (S.tp, S.tm, unit) tele) : S.tp m =
  let+ (tps, _) = telescope tele
  in S.Record tps

let tp_meta_abs (tele : (S.tp, S.tm, S.tp) tele) : S.tp m =
  let+ (tele, tp) = telescope tele
  in S.TpMetaAbs (tele, tp)

let shape_univ (tm : S.tm m) : S.tp m =
  let+ tm = tm
  in S.ShapeUniv tm

let el_shape (tm : S.tm m) : S.tp m =
  let+ tm = tm
  in S.ElShape tm

let point_univ (tm : S.tm m) : S.tp m =
  let+ tm = tm
  in S.PointUniv tm
