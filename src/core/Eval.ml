open Bwd

module S = Syntax
module V = Value

module TB = TermBuilder

module Internal =
struct
  let rec eval (env : V.env) (tm : S.tm) : V.tm =
    match tm with
     | S.Var ix ->
        Lazy.force (Bwd.nth env.tms ix)
     | S.Lam body ->
        V.Lam { env; body }
     | S.App (tm1, tm2) ->
        let v1 = eval env tm1 in
        let v2 = Lazy.from_fun @@ fun () -> eval env tm2 in
        do_app v1 v2
     | S.Pair (tm1, tm2) ->
        let v1 = Lazy.from_fun @@ fun () -> eval env tm1 in
        let v2 = Lazy.from_fun @@ fun () -> eval env tm2 in
        V.Pair (v1, v2)
     | S.Fst tm ->
        do_fst (eval env tm)
     | S.Snd tm ->
        do_snd (eval env tm)
     | S.CodeUniv ->
        V.CodeUniv
     | S.CodePi (tm1, tm2) ->
        V.CodePi (eval env tm1, eval env tm2)
     | S.CodeSigma (tm1, tm2) ->
        V.CodeSigma (eval env tm1, eval env tm2)
     | S.DimZero ->
        V.DimZero
     | S.DimSuc tm ->
        V.DimSuc (eval env tm)
     | S.Eps ->
        V.Point []
     | S.Shape tms ->
        V.Shape (Bwd.map (fun (lbl, tm) -> (lbl, eval env tm)) tms)
     | S.Zero tm ->
        do_zero (eval env tm)
     | S.One tm ->
        do_one (eval env tm)
     | S.DimRec { mot; zero; suc; scrut } ->
        do_dim_rec env mot (eval env zero) (eval env suc) (eval env scrut)

  and eval_tp (env : V.env) (tp : S.tp) : V.tp =
    match tp with
    | S.TpVar ix ->
        Lazy.force (Bwd.nth env.tps ix)
    | S.Univ ->
       V.Univ
    | S.El tm ->
       do_el (eval env tm)
    | S.Pi (a, b) ->
       V.Pi (eval_tp env a, { env; body = b })
    | S.Sigma (a, b) ->
       V.Pi (eval_tp env a, { env; body = b })
    | S.TpDim ->
       V.TpDim
    | S.TpShape tm ->
       V.TpShape (eval env tm)
    | S.TpPoint (tm1, tm2) ->
       V.TpPoint (eval env tm1, eval env tm2)

  and inst_tm_clo (clo : S.tm V.clo) (v : V.tm Lazy.t) : V.tm =
    eval (V.Env.extend_tm clo.env v) clo.body

  and inst_tp_clo (clo : S.tp V.clo) (v : V.tm Lazy.t) : V.tp =
    eval_tp (V.Env.extend_tm clo.env v) clo.body

  and do_app (vfn : V.tm) (varg : V.tm Lazy.t) : V.tm =
    match vfn with
    | V.Lam clo ->
       inst_tm_clo clo varg
    | V.Neu (neu, V.Pi (a, b)) ->
       V.Neu ({ neu with spine = V.App (varg, a) :: neu.spine }, inst_tp_clo b varg)
    |  _ ->
        failwith "bad do_app"

  and do_apps (vfn : V.tm) (vargs : V.tm Lazy.t list) : V.tm =
    List.fold_left do_app vfn vargs

  and do_fst (v : V.tm) : V.tm =
    match v with
    | V.Pair (v1 , _) ->
       Lazy.force v1
    | V.Neu (neu, V.Sigma (a, _)) ->
       V.Neu ({ neu with spine = V.Fst :: neu.spine }, a)
    | _ ->
       failwith "bad do_fst"

  and do_snd (v : V.tm) : V.tm =
    match v with
    | V.Pair (_, v2) ->
       Lazy.force v2
    | V.Neu (neu, V.Sigma (a, b)) ->
       let vfst = Lazy.from_val @@ V.Neu ({ neu with spine = V.Fst :: neu.spine }, a) in
       V.Neu ({ neu with spine = V.Snd :: neu.spine }, inst_tp_clo b vfst)
    | _ ->
       failwith "bad do_fst"

  and do_zero (omega : V.tm) : V.tm =
    match omega with
    | V.Point pt ->
       V.Point (false :: pt)
    | V.Shape omegas ->
       V.Shape (Bwd.map (fun (lbl, omega) -> (lbl, do_zero omega)) omegas)
    | V.Neu (neu, V.TpShape d) ->
       V.Neu ({ neu with spine = Zero :: neu.spine }, V.TpShape (V.DimSuc d))
    | _ ->
       failwith "bad do_zero"

  and do_one (omega : V.tm) : V.tm =
    match omega with
    | V.Point pt ->
       V.Point (true :: pt)
    | V.Shape omegas ->
       V.Shape (Bwd.map (fun (lbl, omega) -> (lbl, do_zero omega)) omegas)
    | V.Neu (neu, V.TpShape d) ->
       V.Neu ({ neu with spine = One :: neu.spine }, V.TpShape (V.DimSuc d))
    | _ ->
       failwith "bad do_zero"

  and do_dim_rec (env : V.env) (mot : S.tp) (zero : V.tm) (suc : V.tm) (scrut : V.tm) =
    match scrut with
    | V.DimZero ->
       zero
    | V.DimSuc d ->
       do_apps suc [Lazy.from_val d; Lazy.from_fun @@ fun () -> do_dim_rec env mot zero suc d]
    | V.Neu (neu, V.TpDim) ->
       let tp = eval_tp (V.Env.extend_tm env (Lazy.from_val scrut)) mot in
       V.Neu ({ neu with spine = V.DimRec { mot = { env; body = mot }; zero; suc } :: neu.spine }, tp)
    | _ ->
       failwith "bad do_zero"

  and do_el (v : V.tm) : V.tp =
    match v with
    | V.Neu (neu, V.Univ) ->
       V.ElNeu neu
    | V.CodeUniv ->
       V.Univ
    | V.CodePi (code_a, code_b) ->
       splice_tp @@
       Splice.tm code_a @@ fun a ->
       Splice.tm code_b @@ fun b ->
       Splice.build @@
       TB.pi (TB.el a) @@ fun x -> TB.el (TB.app b x)
    | V.CodeSigma (code_a, code_b) ->
       splice_tp @@
       Splice.tm code_a @@ fun a ->
       Splice.tm code_b @@ fun b ->
       Splice.build @@
       TB.sigma (TB.el a) @@ fun x -> TB.el (TB.app b x)
    | _ ->
       failwith "bad do_el"

  and splice (splice : S.tm Splice.m) : V.tm =
    let (tm , env) = Splice.run V.Env.empty splice in
    eval env tm

  and splice_tp (splice : S.tp Splice.m) : V.tp =
    let (tp , env) = Splice.run V.Env.empty splice in
    eval_tp env tp
end
