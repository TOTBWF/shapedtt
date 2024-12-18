(** Mediating between syntax and values. *)

module S = Syntax
module V = Value

module TB = TermBuilder

type 'a m = V.env -> 'a TB.m * V.env

let tm (v : V.tm) (k : S.tm TB.m -> 'a m) : 'a m =
  fun env ->
  k (TB.var env.tmlen) (V.Env.extend_tm env (Lazy.from_val v))

let tp (v : V.tp) (k : S.tp TB.m -> 'a m) : 'a m =
  fun env ->
  k (TB.tpvar env.tmlen) (V.Env.extend_tp env (Lazy.from_val v))

let build (tb : 'a TB.m) : 'a m =
  fun env -> tb, env

let run (env : V.env) (a : 'a m) : 'a * V.env =
  let (tb , env) = a env in
  (TB.run ~tplen:env.tplen ~tmlen:env.tmlen tb, env)
