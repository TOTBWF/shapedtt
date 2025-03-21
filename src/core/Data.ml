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
    (** De-Bruijn indexed variables. *)

    | DimZero
    (** The zero dimension. *)

    | DimSucc of tm
    (** The successor dimension. *)

    | Lam of tm
    (** Lambda abstraction. *)

    | App of tm * tm
    (** Function application. *)

    | Tuple of tm List.t
    (** Introduction form for record types. *)

    | Proj of tm * Idx.t
    (** Elimination form for record types. *)

    | Pt
    (** The point. *)

    | Compound of tm List.t
    (** Introduction form for shapes. *)

    | AppZero of tm
    (** Apply zero to a code. *)

    | Inst of meta_tm * tm
    (** Instantiate a meta-abstracted term. *)

    | DimRec of { mot : tp; zero : tm; succ : tm; scrut : tm }
    (** Eliminate a dimension into a virtual type. *)


  (** Meta-abstracted terms. This is like the judgement form for terms,
      but with more precise control over dependencies. *)
  and meta_tm =
    | MetaAbs of tm
    (** Form a meta-abstracted term. *)

    | AppOne of tm
    (** Applying one to a either a shape or a point yields a meta-abstraction. *)

    | MetaAppZero of meta_tm
    (** Applying zero to a meta-abstraction yields another meta-abstraction. *)

    | MetaAppOne of meta_tm
    (** Applying one to a meta-abstraction yields another meta-abstraction. *)


  and tp =
    | TpVar of Idx.t
    (** Type variables.

        These only exist to be able to use our HOAS machinery for writing types,
        and will always get evaluated away. As such, they do not have a corresponding neutral
        form. *)

    | Dim
    (** The virtual type of dimensions. *)

    | Pi of tp * tp
    (** Pi types. *)

    | Record of tp List.t
    (** Record types. *)

    | TpInst of meta_tp * tm
    (** Instantiation of a meta-abstracted type. *)

    | ShapeUniv of tm
    (** The virtual type of shapes, indexed by a dimension. *)

    | ElShape of tm
    (** Decodes a shape into a into a type by mapping compound shapes to record types. *)

    | PointUniv of tm
    (** The virtual type of points, indexed by a dimension. *)

    | ElPoint of tm
    (** Decodes points to types. Note that this does not compute on Pt. *)

  (** The judgement form meta-abstracted types. *)
  and meta_tp =
    | TpMetaAbs of tp
    (** Form a meta-abstracted type. *)

end = Syntax

(** {0} Values *)
and Value : sig
  type tm =
    | Neu of neu
    (** Neutrals. *)

    | DimZero
    (** The zero dimension. *)

    | DimSucc of tm
    (** The successor dimension. *)

    | Lam of Syntax.tm clo

    | Tuple of tm Lazy.t List.t
    (** Introduction form for record types.
        We opt to make the fields lazy to avoid redundant computation. *)

    | Compound of Syntax.tm List.t clo
    (** Introduction form for shapes. *)

  (** Meta-abstracted values. *)
  and meta_tm =
    | MetaNeu of meta_neu

    | MetaAbs of Syntax.tm clo
    (** Form a meta-abstracted term. *)

  and tp =
    | Dim
    (** The virtual type of dimensions. *)

    | Pi of tp * Syntax.tp clo
    (** Pi types. *)

    | Record of Syntax.tp List.t clo
    (** Record types. *)

    | ShapeUniv of tm

    | ElShape of neu

    | PointUniv of tm

    | ElPoint of neu

  (** Meta-abstracted types. *)
  and meta_tp =
    | TpMetaAbs of Syntax.tp clo
    (** Form a meta-abstracted type. *)

  and neu = { hd : hd; spine : frm List.t; zeros : int }

  (** A neutral head is something that computation got stuck on. *)
  and hd =
    | Var of Lvl.t
    (** De-Bruijn level variables. *)
    | Pt
    (** The point is a postulate, so it should be a neutral, not a value. *)
    | Inst of meta_neu * tm Lazy.t
    (** Meta-neutrals are the only way instantiation get blocked. *)

  and frm =
    | App of tm Lazy.t
    | Proj of Idx.t
    | DimRec of { mot : tp; zero : tm; succ : tm }

  and meta_neu = { meta_hd : meta_hd; meta_spine : meta_frm List.t }

  (** Meta-abstracted terms are their own judgement, so they have their own neutrals. *)
  and meta_hd =
    | AppOne of neu

  and meta_frm =
    | MetaAppZero
    | MetaAppOne

  and env =
    { tms : tm Lazy.t List.t;
      tmlen : int;
      tps : tp Lazy.t List.t;
      tplen : int
    }

  and 'a clo = { body : 'a; env : env }

end = Value

module S = Syntax
module V = Value
