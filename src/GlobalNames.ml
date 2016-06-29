(** All global names must be valid C identifiers and globally-unique... *)

open Error
open Idents

let c_of_original = Hashtbl.create 41
let used_c_names: (string, unit) Hashtbl.t = Hashtbl.create 41

let record original_name =
  match Hashtbl.find c_of_original original_name with
  | exception Not_found ->
      let unique_c_name = mk_fresh original_name (Hashtbl.mem used_c_names) in
      Hashtbl.add c_of_original original_name unique_c_name;
      unique_c_name
  | _ ->
      throw_error "Duplicate global name: %s" original_name

let translate name =
  try
    Hashtbl.find c_of_original name
  with Not_found ->
    throw_error "Unresolved global name: %s" name
