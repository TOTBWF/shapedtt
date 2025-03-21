module StringMap = Map.Make (String)
(* type opts = *)
(*   | Group of string * int option * opts List.t *)
module Config =
struct
  type verbosity =
    | None
    | All
    | Verbose of int

  type t =
    | Group of { verbosity : verbosity; children : t StringMap.t }

  let disabled : t = Group { verbosity = None; children = StringMap.empty }

  let all_enabled : t = Group { verbosity = All; children = StringMap.empty }

  let set (key : string) (verbosity : verbosity) (conf : t) : t =
    let rec go =
      function
      | ([], Group group) ->
        Group { group with verbosity }
      | (seg :: segs, Group group) ->
        let upsert =
          function
          | Some conf -> Some (go (segs, conf))
          | None -> Some (go (segs, Group { verbosity = None; children = StringMap.empty }))
        in Group { group with children = StringMap.update seg upsert group.children }
    in go (String.split_on_char '.' key, conf)

  let get (key : string) (conf : t) : verbosity =
    let rec go =
      function
      | ([], Group group) ->
        group.verbosity
      | (seg :: segs, Group group) ->
        match StringMap.find_opt seg group.children with
        | Some conf -> go (segs, conf)
        | None -> group.verbosity
     in go (String.split_on_char '.' key, conf)
end

let debug_config = ref Config.disabled

let set_verbosity ?(prefix = "") (verbosity : Config.verbosity) =
  debug_config := Config.set prefix verbosity !debug_config

let debug_formatter prefix lvl =
  match Config.get prefix !debug_config with
  | All -> Some Format.err_formatter
    | Verbose v ->
      if lvl < v then
        Some Format.err_formatter
      else
        None
    | _ -> None

let print ?(prefix = "") ?(level = 0) (k : unit -> Format.formatter -> unit) =
  match debug_formatter prefix level with
  | Some fmt ->
    Format.kfprintf (k ()) fmt "%s:%d@." prefix level;
    Format.pp_print_newline fmt ()
  | None -> ()

let trace ?(prefix = "") ?(level = 0) (k : 'a -> Format.formatter -> unit) (x : 'a) : 'a =
  print ~prefix ~level (fun _ -> k x);
  x
