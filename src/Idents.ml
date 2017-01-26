(** Manipulation of identifiers *)

module LidMap = Map.Make(struct
  type t = string list * string
  let compare = compare
end)

let string_of_lident (idents, ident) =
  if List.length idents > 0 then
    String.concat "_" idents ^ "_" ^ ident
  else
    ident

let to_c_identifier name =
  let is_valid = function
    | 'a'..'z' | 'A'..'Z' | '0'..'9' | '_' -> true
    | _ -> false
  in
  String.map (fun c -> if not (is_valid c) then '_' else c) name

let mk_fresh name test =
  let name = to_c_identifier name in
  if test name then
    let i = ref 0 in
    let mk () = name ^ string_of_int !i in
    while test (mk ()) do
      incr i
    done;
    mk ()
  else
    name

let fstar_name_of_mod =
  String.map (function '.' -> '_' | x -> x)
