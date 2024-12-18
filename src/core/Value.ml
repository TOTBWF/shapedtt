open Bwd
open Data

include Value

module Env =
struct
  type t = Value.env

  let extend_tm (env : t) (v : tm Lazy.t) : t =
    { env with tms = Bwd.Snoc (env.tms, v); tmlen = env.tmlen + 1 }

  let extend_tp (env : t) (tp : tp Lazy.t) : t =
    { env with tps = Bwd.Snoc (env.tps, tp); tplen = env.tplen + 1 }

  let empty : t =
    { tms = Bwd.Emp; tmlen = 0; tps = Bwd.Emp; tplen = 0 }
end
