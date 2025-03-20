open Core

module S = Syntax
module V = Value

module TB = TermBuilder

let bdry : V.tm =
  Eval.splice_tm @@
  Splice.build @@
  let mot d =
    TB.record @@
    TB.cons (TB.shape_univ d) @@ fun s ->
    TB.cons (TB.tp_meta_abs (TB.el_shape s) @@ fun _ -> TB.point_univ d) @@ fun _ ->
    TB.nil
  and zero =
    TB.tuple [TB.compound TB.nil; TB.meta_abs @@ fun _ -> TB.pt]
  and succ =
    TB.meta_abs @@ fun _ ->
    TB.meta_abs @@ fun sp ->
    let s = TB.proj sp 0
    and p = TB.proj sp 1
    in
    TB.tuple [
      TB.compound
        (TB.cons (TB.digit false s) @@ fun da ->
         TB.cons (TB.inst (TB.digit false p) da) @@ fun _ ->
         TB.cons (TB.inst (TB.digit true s) da) @@ fun _ ->
         TB.nil);
      TB.meta_abs @@ fun ba ->
      TB.inst (TB.digit true p) (TB.tuple [TB.proj ba 0; TB.proj ba 2; TB.proj ba 1])
    ]
  in
  TB.meta_abs @@ fun d ->
  TB.dim_rec mot zero succ d

let bdry_n (n : int) =
  Eval.splice_tm @@
  Splice.tm bdry @@ fun bdry ->
  Splice.build @@
  TB.inst bdry (TB.dim_lit n)

let () = Format.printf "bdry :=@.  %a@." SExpr.dump (V.tm_sexpr bdry)
let () = Format.printf "bdry_0 :=@.  %a@." SExpr.dump (V.tm_sexpr (bdry_n 0))
let () = Format.printf "bdry_1 :=@.  %a@." SExpr.dump (S.tm_sexpr @@ Quote.quote_tm 0 (bdry_n 1))
