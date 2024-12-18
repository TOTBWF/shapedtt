(** The core datatypes of {v shapedtt v}. *)

open Bwd

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
  (** The syntax of terms. *)
  type tm =
    | Var of Idx.t

    | Lam of tm
    | App of tm * tm

    | Pair of tm * tm
    | Fst of tm
    | Snd of tm

    | CodeUniv
    | CodePi of tm * tm
    | CodeSigma of tm * tm

    | DimZero
    (** Dimension zero. *)

    | DimSuc of tm
    (** Dimension successor. *)

    | Eps
    (** The point. *)

    | Shape of (string * tm) Bwd.t
    (** Compound shapes. *)

    | Zero of tm
    (** Apply 0 to a point/shape *)

    | One of tm
    (** Apply 1 to a point/shape *)


  (** The syntax of types. *)
  type tp =
    | TpVar of Idx.t
    (** Type variables.
        These are only used during splicing, and are never bound by terms.
        Therefore, we do not need to add corresponding neutral forms, as
        they are always evaluated away. *)

    | Univ
    | El of tm
    | Pi of tp * tp
    | Sigma of tp * tp

    | TpDim
    (** The virtual type of dimensions. *)

    | TpShape of tm
    (** The virtual type of shapes. *)

    | TpPoint of tm * tm
    (** The virtual type of points. *)
end = Syntax

(** {0} Values *)
and Value : sig
  (** The syntax of values. *)
  type tm =
    | Neu of neu * tp

    | Lam of Syntax.tm clo

    | Pair of tm Lazy.t * tm Lazy.t

    | CodeUniv
    | CodePi of tm * tm
    | CodeSigma of tm * tm

    | DimZero
    (** Dimension zero. *)

    | DimSuc of tm
    (** Dimension successor. *)

    | Point of bool list
    (** The point. *)

    | Shape of (string * tm) Bwd.t
    (** Compound shapes. *)

  and tp =
    | ElNeu of neu
    | Univ
    | Pi of tp * Syntax.tp clo
    | Sigma of tp * Syntax.tp clo

    | TpDim
    (** The virtual type of dimensions. *)

    | TpShape of tm
    (** The virtual type of shapes. *)

    | TpPoint of tm * tm
    (** The virtual type of points. *)

  (** Environments.

      We make environments lazy to avoid performing
      potentially useless normalization during evaluation.

      Invariant: All lazy values *must* be effect free.
      Invariant: Bwd.length tms = tmlen.
      Invariant: Bwd.length tps = tplen.
  *)
  and env = { tms : tm Lazy.t bwd; tmlen : int; tps : tp Lazy.t bwd; tplen : int }

  (** Closures. *)
  and 'a clo = { env : env; body : 'a }

  (** A {!type:neu} is a value that is blocked on the computation of a {!type:hd} (pronounced "head").
      When the head becomes unblocked, the list of stuck computation frames {!type:frame} will resume computation.
  *)
  and neu = { hd : hd; spine : frame list }

  (** A head is a variable {!constructor:Var}. *)
  and hd =
    | Var of Lvl.t

  (** Neutral frames; these correspond to the elimination forms of the type theory. *)
  and frame =
    | App of tm Lazy.t * tp
    | Fst
    | Snd

    | Zero
    (** Apply 0 to a shape *)

    | One
    (** Apply 1 to a shape *)
end = Value
