(** KreMLin, a tool to translate from a minimal ML-like language to C. *)

let _ =
  let arg_print_ast = ref false in
  let arg_print_json = ref false in
  let arg_print_simplify = ref false in
  let arg_print_c = ref false in
  let arg_write = ref false in
  let arg_out = ref false in
  let arg_compile = ref false in
  let arg_warn_error = ref "" in
  let filename = ref "" in
  let usage = "KreMLin: from a ML-like subset to C\n\
    Usage: " ^ Sys.argv.(0) ^ " [OPTIONS] FILE\n"
  in
  Arg.parse [
    "-dast", Arg.Set arg_print_ast, " pretty-print the input AST";
    "-djson", Arg.Set arg_print_json, " dump the input AST as JSON";
    "-dsimplify", Arg.Set arg_print_simplify, " pretty-print the input AST after simplification";
    "-dc", Arg.Set arg_print_c, " pretty-print the output C";
    "-warn-error", Arg.Set_string arg_warn_error, "  Decide which errors are fatal / warnings / silent.";
    "-no-prefix", Arg.Set Options.no_prefix, " don't prepend the module name to each declaration";
    "-add-include",
      Arg.String (fun s -> Options.add_include := s :: !Options.add_include),
      " prepend #include the-argument to the generated file";
    "-out", Arg.Set arg_out, " output directory for .c and .h files";
    "-write", Arg.Set arg_write, " write an output C file for each file contained in the input file";
    "-compile", Arg.Set arg_compile, " compile .c files and generate an executable";
  ] (fun f ->
    (* TODO: match if .o or something else *)
    filename := f
  ) usage;

  if !filename = "" then begin
    print_endline usage;
    exit 1
  end;

  (* First enable the default warn-error string. *)
  Warnings.parse_warn_error !Options.warn_error;

  (* Then refine that based on the user's preferences. *)
  if !arg_warn_error <> "" then
    Warnings.parse_warn_error !arg_warn_error;

  let print f files =
    let open PPrint in
    Printf.printf "Read [%s]. Printing with w=%d\n" !filename Utils.twidth;
    Print.print (f files ^^ hardline)
  in

  let files = Ast.read_file !filename in
  if !arg_print_ast then
    print PrintAst.print_files files;

  if !arg_print_json then
    Yojson.Safe.to_channel stdout (Ast.binary_format_to_yojson (Ast.current_version, files));

  Checker.check_everything files;
  let files = Simplify.simplify files in

  if !arg_print_simplify then
    print PrintAst.print_files files;
  Checker.check_everything files;

  let files = AstToCStar.translate_files files in
  let files = CStarToC.mk_files files in
  if !arg_print_c then
    print PrintC.print_files files;

  if !arg_write then begin
    flush stderr;
    Printf.printf "KreMLin: writing out C files for %s\n" (String.concat ", " (List.map fst files));
    Output.write files
  end
