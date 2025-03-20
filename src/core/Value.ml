open Data

include Value

module Lvl = Lvl

module Env =
struct
  type t = Value.env

  let extend_tm (env : t) (v : tm Lazy.t) : t =
    { env with tms = v :: env.tms; tmlen = env.tmlen + 1 }

  let extend_tms (env : t) (vs : tm Lazy.t List.t) : t =
    { env with tms = vs @ env.tms; tmlen = env.tmlen + List.length vs }

  let extend_tp (env : t) (tp : tp Lazy.t) : t =
    { env with tps =  tp :: env.tps; tplen = env.tplen + 1 }

  let nth_tm (env : t) (ix : Idx.t) : V.tm Lazy.t =
    List.nth env.tms ix

  let nth_tp (env : t) (ix : Idx.t) : V.tp Lazy.t =
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
