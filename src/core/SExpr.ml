(** Helpers for s-expression printing *)

type t =
  | List of t List.t
  | Atom of String.t

let list (es : t List.t) : t = List es

let atom (s : String.t) : t = Atom s

let int (i : Int.t) : t = Atom (Int.to_string i)

let bool (b : Bool.t) : t = int (Bool.to_int b)

let fn (s : String.t) (es : t List.t) = List (Atom s :: es)

let rec dump (fmt : Format.formatter) (e : t) =
  match e with
  | List es ->
    Format.fprintf fmt "@[<hov 2>(%a)@]" (Format.pp_print_list ~pp_sep:Format.pp_print_space dump) es
  | Atom s ->
    Format.pp_print_string fmt s
