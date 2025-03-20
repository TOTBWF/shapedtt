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

    | Inst of tm * tm
    (** Instantiate a meta-abstracted term. *)

    | Digit of bool * tm

    | DimRec of { mot : tp; zero : tm; succ : tm; scrut : tm }

  and tp =
    | TpVar of Idx.t
    (** Type variables.

        These only exist to be able to use our HOAS machinery for writing types,
        and will always get evaluated away. As such, they do not have a corresponding neutral
        form. *)

    | Dim
    (** The virtual type of dimensions. *)

    | Record of tp List.t
    (** Record types. *)

    | TpMetaAbs of tp * tp
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
    | TpMetaAbs of tp * Syntax.tp clo
    | ShapeUniv of tm
    | ElShape of neu
    | PointUniv of tm
    | ElPoint of neu

  and neu = { hd : hd; spine : frm List.t }

  and hd = Lvl.t

  and frm =
    | Proj of Idx.t
    | Inst of tm Lazy.t
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
