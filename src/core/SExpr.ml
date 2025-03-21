(** Helpers for s-expression printing *)

type t =
  | List of t List.t
  | Vec of t List.t
  | Atom of String.t

let list (es : t List.t) : t = List es

let vec (es : t List.t) : t = Vec es

let atom (s : String.t) : t = Atom s

let prop (s : String.t) : t = Atom (String.cat ":" s)

let int (i : Int.t) : t = Atom (Int.to_string i)

let bool (b : Bool.t) : t = int (Bool.to_int b)

let fn (s : String.t) (es : t List.t) = List (Atom s :: es)

(** Pretty-print an S-expression. *)
let rec pp_print_sexpr (fmt : Format.formatter) (e : t) =
  match e with
  | List es ->
    Format.fprintf fmt "@[<hov 2>(%a)@]" (Format.pp_print_list ~pp_sep:Format.pp_print_space pp_print_sexpr) es
  | Vec es ->
    Format.fprintf fmt "@[<hov 2>[%a]@]" (Format.pp_print_list ~pp_sep:Format.pp_print_space pp_print_sexpr) es
  | Atom s ->
    Format.pp_print_string fmt s
