type t

val mk_ocaml_bindings:
  (CStar.ident * CStar.decl list) list ->
  GlobalNames.mapping ->
  (Ast.lident -> string option) ->
  t

val write_gen_module: public:Bundles.StringSet.t -> internal:Bundles.StringSet.t -> t -> unit
val write_bindings: t -> unit

val file_list: t -> string list
