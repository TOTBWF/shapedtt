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

let run ~tplen ~tmlen (tb : 'a m) : 'a =
  tb { tplen; tmlen }

let with_var (k : S.tm m -> 'a m) : 'a m =
  fun env -> k (var env.tmlen) { env with tmlen = env.tmlen + 1 }

(** {0} Higher-Order Abstract Syntax interface for environment-relative terms. *)
let lam (body : S.tm m -> S.tm m) : S.tm m =
  let+ body = with_var body
  in S.Lam body

let app (fn : S.tm m) (arg : S.tm m) : S.tm m =
  let+ fn = fn
  and+ arg = arg
  in S.App (fn, arg)

let el (a : S.tm m) : S.tp m =
  let+ a = a
  in S.El a

let pi (a : S.tp m) (b : S.tm m -> S.tp m) : S.tp m =
  let+ a = a
  and+ b = with_var b
  in S.Pi (a, b)

let sigma (a : S.tp m) (b : S.tm m -> S.tp m) : S.tp m =
  let+ a = a
  and+ b = with_var b
  in S.Sigma (a, b)
