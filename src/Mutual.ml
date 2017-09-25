(** Monormophization of data types, including tuples, then compilation of
 * pattern matches and of data types into structs & unions. *)

 open Ast

 module K = Constant

 let flatten_mutual : decl -> decl list =
 function
   | DTypeMutual type_decls ->
    List.fold_right (fun ty_decl os ->
      match ty_decl with
      | DType(n, flags, arity, def, _) -> DType(n, flags, arity, def, true) :: os
      | _ -> assert false) type_decls []
   | d -> [d]

 let remove_mutual_types files =
   List.map (fun (file, ds) ->
     (file, KList.map_flatten flatten_mutual ds)) files
