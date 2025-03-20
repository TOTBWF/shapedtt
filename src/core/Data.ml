(** The core datatypes of {v shapedtt v}. *)

(** {0} Variables *)

(** De Bruijn indices. *)
module Idx =
struct
  type t = int
end

(** De Bruijn levels. *)
module Lvl =
struct
  type t = int
end

(** {0} Syntax *)
module rec Syntax : sig

  type tm =
    | Var of Idx.t

    | DimZero

    | DimSucc of tm

    | Tuple of tm List.t
    (** Introduction form for record types. *)

    | Proj of tm * Idx.t
    (** Elimination form for record types. *)

    | Pt

    | Compound of tm List.t
    (** Introduction form for shapes. *)

    | MetaAbs of tm
    (** Meta-abstraction of terms. *)

    | Inst of tm * tm List.t
    (** Instantiate a meta-abstracted term. *)

    | Digit of bool * tm

    | DimRec of { mot : tp; zero : tm; succ : tm; scrut : tm }

  and tp =
    | Dim
    (** The virtual type of dimensions. *)

    | Record of tp List.t
    (** Record types. *)

    | MetaAbs of tp List.t * tp
    (** Meta-abstraction of types *)

    | ShapeUniv of tm
    (** The virtual type of shapes. *)

    | ElShape of tm
    (** Decodes a shape into a into a type by mapping compound shapes to record types. *)

    | PointUniv of tm
    (** The virtual type of points. *)

    | ElPoint of tm
    (** Unclear what this does :) *)

end = Syntax

(** {0} Values *)
and Value : sig
  type tm =
    | Neu of neu
    | DimZero
    | DimSucc of tm
    | Tuple of tm Lazy.t List.t
    | Pt
    | Compound of (Syntax.tm, tm) tele
    | MetaAbs of Syntax.tm clo

  and tp =
    | Dim
    | Record of (Syntax.tp, tp) tele
    | MetaAbs of (Syntax.tp, tp) tele * Syntax.tp clo
    | ShapeUniv of tm
    | ElShape of neu
    | PointUniv of tm
    | ElPoint of neu

  and neu = { hd : hd; spine : frm List.t }

  and hd = Lvl.t

  and frm =
    | Proj of Idx.t
    | Inst of tm Lazy.t List.t
    | Digit of bool
    | DimRec of { mot : tp; zero : tm; succ : tm }

  and env =
    { tms : tm Lazy.t List.t;
      tmlen : int;
      tps : tp Lazy.t List.t;
      tplen : int
    }

  and 'a clo = { body : 'a; env : env }

  and ('s, 'v) tele =
    | Nil
    | Cons of 'v * 's list clo

end = Value

module S = Syntax
module V = Value

(* n : Dim ⊢ ○ n shapeⁿ *)
let bdry : S.tm =
  S.DimRec
    { mot = S.Record [S.ShapeUniv (S.Var 0); S.MetaAbs ([S.ElShape (S.Var 0)], S.PointUniv (S.Var 1))];
      zero = S.Tuple [S.Compound []; S.MetaAbs S.Pt];
      succ =
        (* n : Dim, sp : Σ (○a : Shape n) (El ○a ⇒ Point n) ⊢ Σ (○a : Shape (suc n)) (El ○a ⇒ Point (suc n)) *)
        S.Tuple [
          S.Compound [
            (* n : Dim, sp : Σ (○a : Shape n) (El ○a ⇒ Point n) ⊢ Shape (suc n) *)
            S.Digit (false, S.Proj (S.Var 0, 0));
            (* n : Dim, sp : Σ (○a : Shape n) (El ○a ⇒ Point n), ∂a : 𝟘 sp.0 ⊢ Shape (suc n) *)
            S.Inst (S.Digit (false, S.Proj (S.Var 1, 1)), [S.Var 0]);
            (* n : Dim, sp : Σ (○a : Shape n) (El ○a ⇒ Point n), ∂a : 𝟘 sp.0, a : 𝟘 (sp.1 ∂a) ⊢ Shape (suc n) *)
            S.Inst (S.Digit (true, S.Proj (S.Var 2, 0)), [S.Var 1])
          ];
          (* n : Dim, sp : Σ (○a : Shape n) (El ○a ⇒ Point n) ⊢ El ○a ⇒ Point (suc n) *)
          S.MetaAbs (
            (* n : Dim, sp : Σ (○a : Shape n) (El ○a ⇒ Point n), s' : El ○a ⊢ Point (suc n) *)
            S.Inst (
              S.Digit (true, S.Proj (S.Var 1, 1)),
              (* n : Dim, sp : Σ (○a : Shape n) (El ○a ⇒ Point n), s' : El ○a ⊢ t0 : 𝟘 sp.0 *)
              (* n : Dim, sp : Σ (○a : Shape n) (El ○a ⇒ Point n), s' : El ○a ⊢ t1 : (𝟙 sp.0) @ s'.0 *)
              (* n : Dim, sp : Σ (○a : Shape n) (El ○a ⇒ Point n), s' : El ○a ⊢ t2 : 𝟘 (sp.1 @ s'.0) *)
              [S.Proj (S.Var 0, 0); S.Proj (S.Var 0, 2); S.Proj (S.Var 0, 1)])
          )
        ];
      scrut = S.Var 0;
    }
