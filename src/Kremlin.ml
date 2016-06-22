(** KreMLin, a tool to translate from a minimal ML-like language to C. *)

let _ =
  let arg_print_ast = ref false in
  let arg_print_simplify = ref false in
  let arg_print_c = ref false in
  let arg_write = ref false in
  let filename = ref "" in
  let usage = "KreMLin: from a ML-like subset to C\n\
    Usage: " ^ Sys.argv.(0) ^ " [OPTIONS] FILE\n"
  in
  Arg.parse [
    "-dast", Arg.Set arg_print_ast, " pretty-print the input AST";
    "-dsimplify", Arg.Set arg_print_simplify, " pretty-print the input AST after simplification";
    "-dc", Arg.Set arg_print_c, " pretty-print the output C";
    "-write", Arg.Set arg_write, " write an output C file for each file contained in the input file";
  ] (fun f ->
    filename := f
  ) usage;

  if !filename = "" then begin
    print_endline usage;
    exit 1
  end;

  let print f files =
    let open PPrint in
    Printf.printf "Read [%s]. Printing with w=%d\n" !filename Utils.twidth;
    Print.print (f files ^^ hardline)
  in

  let files = Ast.read_file !filename in
  if !arg_print_ast then
    print PrintAst.print_files files;

  let files = Simplify.simplify files in

  if !arg_print_simplify then
    print PrintAst.print_files files;

  let files = AstToCStar.translate_files files in
  let files = CStarToC.mk_files files in
  if !arg_print_c then
    print PrintC.print_files files;

  if !arg_write then begin
    Printf.printf "KreMLin: writing out files\n";
    Output.write files
  end
