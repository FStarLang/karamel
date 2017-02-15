(** The type of a single bundle -- this avoids a cyclic dependency between
 * [Parser] and [Bundles] *)

(** Crypto.Chacha20=Crypto.Symmetric.Chacha20.*,Crypto.Flag *)
type t = string list * pat list

and pat =
  | Module of string list
  | Prefix of string list


let string_of_pat pat =
  match pat with
  | Module path ->
      String.concat "." path
  | Prefix path ->
      String.concat "." (path @ [ "*" ])

let string_of_bundle (name, pats) =
  match name with
  | [] ->
      String.concat "," (List.map string_of_pat pats)
  | path ->
      String.concat "." path ^ "=" ^
      String.concat "," (List.map string_of_pat pats)

module LidMap = Idents.LidMap

(* Create a map from an lid to the file it now appears in (after bundling). *)
let mk_file_of files =
  let file_of = List.fold_left (fun map (name, decls) ->
    List.fold_left (fun map decl ->
      LidMap.add (Ast.lid_of_decl decl) name map
    ) map decls
  ) LidMap.empty files in
  let file_of lid =
    try
      Some (LidMap.find lid file_of)
    with Not_found ->
      None
  in
  file_of
