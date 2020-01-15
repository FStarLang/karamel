(* Copyright (c) INRIA and Microsoft Corporation. All rights reserved. *)
(* Licensed under the Apache 2.0 License. *)

(** Manipulation of identifiers *)

module LidMap = Map.Make(struct
  type t = string list * string
  let compare = compare
end)

module LidSet = Set.Make(struct
  type t = string list * string
  let compare = compare
end)


let string_of_lident (idents, ident) =
  if List.length idents > 0 then
    String.concat "_" idents ^ "_" ^ ident
  else
    ident

let to_c_identifier name =
  let b = Buffer.create 256 in
  String.iter (function
    | 'a'..'z' | 'A'..'Z' | '0'..'9' | '_' as c ->
        Buffer.add_char b c
    | '\'' ->
        Buffer.add_string b "_prime"
    | _ ->
        Buffer.add_char b '_'
  ) name;
  Buffer.contents b

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

let module_name lident =
  String.concat "_" (fst lident)
