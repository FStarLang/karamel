type t

val mk_ocaml_bindings:
  (CStar.ident * string list * CStar.decl list) list ->
  (Ast.lident, Ast.ident) Hashtbl.t ->
  (Ast.lident -> string option) ->
  t

val write_gen_module: t -> unit
val write_bindings: t -> unit

val file_list: t -> string list
