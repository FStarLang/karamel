(* Rust-specific transformations *)

open Ast

(* Doesn't make sense in Rust *)
let remove_push_pop_frame = object
  inherit [_] map
  method! visit_EPushFrame _ = EUnit
  method! visit_EPopFrame _ = EUnit
end

let simplify_ast files =
  let files = remove_push_pop_frame#visit_files () files in
  files

