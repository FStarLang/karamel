(** KreMLin, a tool to translate from a minimal ML-like language to C. *)

let main =
  ignore (Ast.read_file, DeBruijn.lift)
