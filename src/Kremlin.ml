(** KreMLin, a tool to translate from a minimal ML-like language to C. *)

let _ =
  let arg_print_ast = ref false in
  let arg_print_c = ref false in
  let filename = ref "" in
  let usage = "KreMLin: from a ML-like subset to C\n\
    Usage: " ^ Sys.argv.(0) ^ " [OPTIONS] FILE\n"
  in
  Arg.parse [
    "-dast", Arg.Set arg_print_ast, " pretty-print the input AST";
    "-dc", Arg.Set arg_print_c, " pretty-print the output C"
  ] (fun f ->
    filename := f
  ) usage;

  if !filename = "" then begin
    print_endline usage;
    exit 1
  end;

  let files = Ast.read_file !filename in
  let files = Simplify.simplify files in
  if !arg_print_ast then begin
    let open PPrint in
    Printf.printf "Read [%s]. Printing with w=%d\n" !filename Utils.twidth;
    Print.print (PrintAst.print_files files ^^ hardline)
  end;

  let files = AstToC.translate_files files in
  if !arg_print_c then begin
    let open PPrint in
    Printf.printf "Read [%s]. Printing with w=%d\n" !filename Utils.twidth;
    Print.print (PrintC.print_files files ^^ hardline)
  end
