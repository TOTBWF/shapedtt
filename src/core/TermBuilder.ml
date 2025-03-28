(** Terms constructed relative to an arbitrary environment. *)

open Data

module S = Syntax
module V = Value

type env = { tplen : int; tmlen : int }

type 'a m = env -> 'a

type ('tp, 'tm) tele =
  | Nil
  | Cons of 'tp m * ('tm m -> ('tp, 'tm) tele)


module Tele =
struct
  let nil : ('tp, 'tm) tele =
    Nil

  let cons (tp : 'tp m) (k : 'tm m -> ('tp, 'tm) tele) : ('tp, 'tm) tele =
    Cons (tp, k)

  let rec map (f : 'tp0 m -> 'tp1 m) (tele : ('tp0, 'tm) tele) : ('tp1, 'tm) tele =
    match tele with
    | Nil ->
      Nil
    | Cons (tp, tele) ->
      Cons (f tp, (fun x -> map f (tele x)))
end

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

let rec telescope (tele : ('tp, S.tm) tele) : 'tp list m =
  match tele with
  | Nil -> pure []
  | Cons (x, k) ->
    let+ x = x
    and+ xs = with_var (fun x -> telescope (k x))
    in x :: xs

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

let pi (base : S.tp m) (fam : S.tm m -> S.tp m) : S.tp m =
  let+ base = base
  and+ fam = with_var fam
  in S.Pi (base, fam)

let lam (body : S.tm m -> S.tm m) : S.tm m =
  let+ body = with_var body
  in S.Lam body

let app (tm : S.tm m) (arg : S.tm m) : S.tm m =
  let+ tm = tm
  and+ arg = arg
  in S.App (tm, arg)

let apps (tm : S.tm m) (args : S.tm m list) : S.tm m =
  List.fold_left app tm args

let tuple (tms : S.tm m list) : S.tm m =
  let+ tms = many tms in
  S.Tuple tms

let proj (tm : S.tm m) (ix : Idx.t) : S.tm m =
  let+ tm = tm in
  S.Proj (tm, ix)

let pt : S.tm m =
  pure S.Pt

let compound (tele : (S.tm, S.tm) tele) : S.tm m =
  let+ tms = telescope tele in
  S.Compound tms

let meta_abs (body : S.tm m -> S.tm m) : S.meta_tm m =
  let+ body = with_var body
  in S.MetaAbs body

let inst (tm : S.meta_tm m) (arg : S.tm m) : S.tm m =
  let+ tm = tm
  and+ arg = arg
  in S.Inst (tm, arg)

let app_zero (tm : S.tm m) : S.tm m =
  let+ tm = tm
  in S.AppZero tm

let app_one (tm : S.tm m) : S.meta_tm m =
  let+ tm = tm
  in S.AppOne tm

let meta_app_zero (tm : S.meta_tm m) : S.meta_tm m =
  let+ tm = tm
  in S.MetaAppZero tm

(** Instantiate every entry of a telescope with the provided argument. *)
let rec inst_tele (tele : (S.meta_tm, S.tm) tele) (arg : S.tm m) : (S.tm, S.tm) tele =
  match tele with
  | Nil -> Nil
  | Cons (tm, k) -> Cons (inst tm arg, fun x -> inst_tele (k x) arg)

let dim_rec (mot : S.tm m -> S.tp m) (zero : S.tm m) (succ : S.tm m) (scrut : S.tm m) =
  let+ mot = with_var mot
  and+ zero = zero
  and+ succ = succ
  and+ scrut = scrut
  in S.DimRec { mot; zero; succ; scrut }

let dim : S.tp m =
  pure S.Dim

let record (tele : (S.tp, S.tm) tele) : S.tp m =
  let+ tps = telescope tele
  in S.Record tps

let shape_univ (tm : S.tm m) : S.tp m =
  let+ tm = tm
  in S.ShapeUniv tm

let el_shape (tm : S.tm m) : S.tp m =
  let+ tm = tm
  in S.ElShape tm

let point_univ (tm : S.tm m) : S.tp m =
  let+ tm = tm
  in S.PointUniv tm
