open Core

module S = Syntax
module V = Value

module TB = TermBuilder

let bdry : V.tm =
  NbE.splice_tm @@
  Splice.build @@
  let mot d =
    TB.record @@
    TB.Tele.cons (TB.shape_univ d) @@ fun s ->
    TB.Tele.cons (TB.pi (TB.el_shape s) @@ fun _ -> TB.point_univ d) @@ fun _ ->
    TB.Tele.nil
  and zero =
    TB.tuple [TB.compound TB.Tele.nil; TB.lam @@ fun _ -> TB.pt]
  and succ =
    TB.lam @@ fun _ ->
    TB.lam @@ fun sp ->
    let s = TB.proj sp 0
    and p = TB.proj sp 1
    in
    TB.tuple [
      TB.compound
        (TB.Tele.cons (TB.app_zero s) @@ fun da ->
         TB.Tele.cons (TB.app_zero (TB.app p da)) @@ fun _ ->
         TB.Tele.cons (TB.inst (TB.app_one s) da) @@ fun _ ->
         TB.Tele.nil);
      TB.lam @@ fun ba ->
      TB.inst (TB.app_one p) (TB.tuple [TB.proj ba 0; TB.proj ba 2; TB.proj ba 1])
    ]
  in
  TB.lam @@ fun d ->
  TB.dim_rec mot zero succ d

let bdry_n (n : int) =
  NbE.splice_tm @@
  Splice.tm bdry @@ fun bdry ->
  Splice.build @@
  TB.proj (TB.app bdry (TB.dim_lit n)) 0

let filler_n (n : int) =
  NbE.splice_tm @@
  Splice.tm bdry @@ fun bdry ->
  Splice.build @@
  TB.proj (TB.app bdry (TB.dim_lit n)) 1


let () = Format.printf "bdry :=@.  %a@." V.dump_tm bdry
let () = Format.printf "bdry_0 :=@.  %a@." S.dump_tm (NbE.quote_tm 0 (bdry_n 0))
let () = Format.printf "filler_0 :=@.  %a@." S.dump_tm (NbE.quote_tm 0 (filler_n 0))
let () = Format.printf "bdry_1 :=@.  %a@." S.dump_tm (NbE.quote_tm 0 (bdry_n 1))
let () = Format.printf "filler_1 :=@.  %a@." S.dump_tm (NbE.quote_tm 0 (filler_n 1))
let () = Format.printf "bdry_2 :=@.  %a@." S.dump_tm (NbE.quote_tm 0 (bdry_n 2))
