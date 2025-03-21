(** Mediating between syntax and values. *)

module S = Syntax
module V = Value

module TB = TermBuilder

type 'a m = V.env -> 'a TB.m * V.env

let build (tb : 'a TB.m) : 'a m =
  fun env -> tb, env

let run (env : V.env) (a : 'a m) : 'a * V.env =
  let (tb , env) = a env in
  TB.run ~tplen:env.tplen ~tmlen:env.tmlen tb, env

let tm (v : V.tm) (k : S.tm TB.m -> 'a m) : 'a m =
  fun env ->
  k (TB.var env.tmlen) (V.Env.extend_tm env (Lazy.from_val v))

let tp (v : V.tp) (k : S.tp TB.m -> 'a m) : 'a m =
  fun env ->
  k (TB.tpvar env.tmlen) (V.Env.extend_tp env (Lazy.from_val v))

let tm_clo (clo : S.tm V.clo) (k : (S.tm TB.m -> S.tm TB.m) -> 'a m) : 'a m =
  tm (V.Lam clo) @@ fun tm ->
  k (fun arg -> TB.app tm arg)

let tm_tele (tele : S.tm List.t V.clo) (k : (S.tm, S.tm) TB.tele -> 'a m) : 'a m =
  let rec lam_abs_tele (env : V.env) (bodies : S.tm list) : V.tm Lazy.t list =
    match bodies with
    | [] -> []
    | (body :: bodies) ->
      let var = Lazy.from_val (V.var env.tmlen) in
      Lazy.from_val (V.Lam { env; body }) :: lam_abs_tele (V.Env.extend_tm env var) bodies

  and app_abs_tele (lvl : V.Lvl.t) (n : int) (args : S.tm TB.m list) : (S.tm, S.tm) TB.tele =
    if n <= 0 then
      Nil
    else
      Cons (TB.apps (TB.var lvl) args,
            fun el_v -> app_abs_tele (lvl + 1) (n - 1) (args @ [el_v]))
  in
  fun env ->
  let skel = app_abs_tele env.tmlen (List.length tele.body) []
  and env = V.Env.extend_tms tele.env (lam_abs_tele tele.env tele.body)
  in k skel env
