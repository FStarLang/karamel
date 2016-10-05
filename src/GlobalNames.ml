(** All global names must be valid C identifiers and globally-unique... *)

open Warnings
open Idents

let c_of_original = Hashtbl.create 41
let used_c_names: (string, unit) Hashtbl.t = Hashtbl.create 41

let record original_name desired_name =
  match Hashtbl.find c_of_original original_name with
  | exception Not_found ->
      let unique_c_name = mk_fresh desired_name (Hashtbl.mem used_c_names) in
      Hashtbl.add c_of_original original_name unique_c_name;
      Hashtbl.add used_c_names unique_c_name ();
      unique_c_name
  | _ ->
      fatal_error "Duplicate global name: %s" original_name

let translate name fallback =
  try
    Hashtbl.find c_of_original name
  with Not_found ->
    (* Assuming some externally-realized function. *)
    to_c_identifier fallback
