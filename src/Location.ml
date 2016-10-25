(** Helpers ----------------------------------------------------------------- *)

open Ast
open PPrint
open PrintCommon

type loc =
  | File of string
  | In of string
  | InTop of lident
  | Then
  | Else
  | After of string

let print_loc = function
  | InTop l ->
      string "in top-level declaration " ^^ print_lident l
  | File f ->
      string "in file " ^^ string f
  | In l ->
      string "in the definition of " ^^ string l
  | Then ->
      string "in the then branch"
  | Else ->
      string "in the else branch"
  | After s ->
      string "after the definition of " ^^ string s

let print_location locs =
  separate_map (string ", ") print_loc locs

let ploc = printf_of_pprint print_location

let update_location old_locs new_loc  =
  match new_loc, old_locs with
  | After _, After _ :: locs ->
      new_loc :: locs
  | _ ->
      new_loc :: old_locs
