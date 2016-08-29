(** KreMLin, a tool to translate from a minimal ML-like language to C. *)

let _ =
  let arg_print_ast = ref false in
  let arg_print_json = ref false in
  let arg_print_simplify = ref false in
  let arg_print_c = ref false in
  let arg_write = ref false in
  let arg_warn_error = ref "" in
  let c_files = ref [] in
  let o_files = ref [] in
  let fst_files = ref [] in
  let filename = ref "" in
  let usage = "KreMLin: from a ML-like subset to C\n\
    Usage: " ^ Sys.argv.(0) ^ " [OPTIONS] FILE\n"
  in
  let found_file = ref false in
  Arg.parse [
    "-dast", Arg.Set arg_print_ast, " pretty-print the input AST";
    "-djson", Arg.Set arg_print_json, " dump the input AST as JSON";
    "-dsimplify", Arg.Set arg_print_simplify, " pretty-print the input AST after simplification";
    "-dc", Arg.Set arg_print_c, " pretty-print the output C";
    "-warn-error", Arg.Set_string arg_warn_error, "  Decide which errors are fatal / warnings / silent.";
    "-verbose", Arg.Set Options.verbose, "  Show the output of intermediary tools when acting as a driver for F* or the C compiler";
    "-no-prefix", Arg.Set Options.no_prefix, " don't prepend the module name to each declaration";
    "-I", Arg.String (fun s -> Options.includes := s :: !Options.includes),
      " add search path";
    "-add-include", Arg.String (fun s -> Options.add_include := s :: !Options.add_include),
      " prepend #include the-argument to the generated file";
    "-tmpdir", Arg.Set_string Options.tmpdir, " temporary directory for .out, .c, .h and .o files";
  ] (fun f ->
    if Filename.check_suffix f ".fst" then
      fst_files := f :: !fst_files
    else if Filename.check_suffix f ".o" then
      o_files := f :: !o_files
    else if Filename.check_suffix f ".c" then
      c_files := f :: !c_files
    else if Filename.check_suffix f ".json" || Filename.check_suffix f ".out" then
      filename := f
    else
      Warnings.fatal_error "Unknown file extension for %s\n" f;
    found_file := true
  ) usage;

  if not !found_file then begin
    print_endline usage;
    exit 1
  end;

  (* First enable the default warn-error string. *)
  Warnings.parse_warn_error !Options.warn_error;

  (* Then refine that based on the user's preferences. *)
  if !arg_warn_error <> "" then
    Warnings.parse_warn_error !arg_warn_error;

  (* Shall we run F* first? *)
  let filename =
    if List.length !fst_files > 0 then
      Driver.run_fstar !fst_files
    else
      !filename
  in

  let print f files =
    let open PPrint in
    Printf.printf "Read [%s]. Printing with w=%d\n" filename Utils.twidth;
    Print.print (f files ^^ hardline)
  in

  let files = Ast.read_file filename in
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
