(** KreMLin, a tool to translate from a minimal ML-like language to C. *)

let _ =
  let arg_print = ref false in
  let filename = ref "" in
  let usage = "KreMLin: from a ML-like subset to C\n\
    Usage: " ^ Sys.argv.(0) ^ " [OPTIONS] FILE\n"
  in
  Arg.parse [
    "-print", Arg.Set arg_print, " pretty-print the input AST"
  ] (fun f ->
    filename := f
  ) usage;

  let files = Ast.read_file !filename in
  if !arg_print then
    let open PPrint in
    Ast.Print.print (Ast.Print.print_files files ^^ hardline)
