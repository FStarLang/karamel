(** Various peephole optimizations *)

open Ast

(* Some helpers ***************************************************************)

let visit_decl (env: 'env) (mapper: 'env map) = function
  | DFunction (ret, name, binders, expr) ->
      DFunction (ret, name, binders, mapper # visit env expr)
  | DTypeAlias t ->
      DTypeAlias t

let visit_program (env: 'env) (mapper: 'env map) (program: program) =
  List.map (visit_decl env mapper) program

let visit_file (env: 'env) (mapper: 'env map) (file: file) =
  let name, program = file in
  name, visit_program env mapper program

let visit_files (env: 'env) (mapper: 'env map) (files: file list) =
  List.map (visit_file env mapper) files


(* The peephole optimizations themselves **************************************)

class dummymatch = object

  inherit [unit] map

  method ematch () e branches =
    match e, branches with
    | EUnit, [ PUnit, body ] ->
        body
    | _ ->
        EMatch (e, branches)

end

let simplify (files: file list): file list =
  let files = visit_files () (new dummymatch) files in
  files


(* TODO: no inner let-bindings, figure out calls to frame, lift definitions at
 * the beginning of the block (or assume C99), etc. *)
