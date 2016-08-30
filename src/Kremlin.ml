(** KreMLin, a tool to translate from a minimal ML-like language to C. *)

let _ =
  let arg_print_ast = ref false in
  let arg_print_json = ref false in
  let arg_print_simplify = ref false in
  let arg_print_c = ref false in
  let arg_skip_compilation = ref false in
  let arg_skip_linking = ref false in
  let arg_warn_error = ref "" in
  let c_files = ref [] in
  let o_files = ref [] in
  let fst_files = ref [] in
  let filename = ref "" in
  let usage = Printf.sprintf
{|KreMLin: from a ML-like subset to C

Usage: %s [OPTIONS] FILES

High-level description:
  1. If some FILES end with .fst, KreMLin will call [fstar] on them to produce [out.krml],
     and jumps to step 2.
  2. If exactly one FILE ends with [.krml] or [.json], or if a [.krml] file was
     produced at step 1., KreMLin will generate a series of [.c] and [.h] files
     in the directory specified by [-tmpdir], or in the current directory.
  3. If some FILES end with [.c], KreMLin will compile them along with the [.c]
     files generated at step 2. to obtain a series of [.o] files.
  4. If some FILES end with [.o], KreMLin will link them along with the [.o] files
     obtained at step 3. to obtain a final executable.

The [-skip-compilation] option will stop KreMLin after step 2.
The [-skip-linking] option will stop KreMLin after step 3.

Supported options:|} Sys.argv.(0)
  in
  let found_file = ref false in
  let prepend r = fun s -> r := s :: !r in
  let spec = [
    "-dast", Arg.Set arg_print_ast, " pretty-print the input AST";
    "-djson", Arg.Set arg_print_json, " dump the input AST as JSON";
    "-dsimplify", Arg.Set arg_print_simplify, " pretty-print the input AST after simplification";
    "-dc", Arg.Set arg_print_c, " pretty-print the output C";
    "-skip-compilation", Arg.Set arg_skip_compilation, " stop after step 2.";
    "-skip-linking", Arg.Set arg_skip_linking, " stop after step 3.";
    "-no-prefix", Arg.String (prepend Options.no_prefix), " don't prepend the module name to declarations from this module";
    "-add-include", Arg.String (prepend Options.add_include), " prepend #include the-argument to the generated file";
    "-tmpdir", Arg.Set_string Options.tmpdir, " temporary directory for .out, .c, .h and .o files";
    "-I", Arg.String (prepend Options.includes), " add directory to search path (F* and C compiler)";
    "-o", Arg.Set_string Options.exe_name, "  name of the resulting executable";
    "-warn-error", Arg.Set_string arg_warn_error, "  decide which errors are fatal / warnings / silent.";
    "-verbose", Arg.Set Options.verbose, "  show the output of intermediary tools when acting as a driver for F* or the C compiler";
  ] in
  let spec = Arg.align spec in
  Arg.parse spec (fun f ->
    if Filename.check_suffix f ".fst" then
      fst_files := f :: !fst_files
    else if Filename.check_suffix f ".o" then
      o_files := f :: !o_files
    else if Filename.check_suffix f ".c" then
      c_files := f :: !c_files
    else if Filename.check_suffix f ".json" || Filename.check_suffix f ".krml" then begin
      if !filename <> "" then
        Warnings.fatal_error "At most one [.json] or [.krml] file supported";
      filename := f
    end else
      Warnings.fatal_error "Unknown file extension for %s\n" f;
    found_file := true
  ) usage;

  if not !found_file ||
     List.length !fst_files = 0 && !filename = "" ||
     List.length !fst_files > 0 && !filename <> ""
  then begin
    print_endline (Arg.usage_string spec usage);
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

  (* -dast *)
  let files = Ast.read_file filename in
  if !arg_print_ast then
    print PrintAst.print_files files;

  (* -djson *)
  if !arg_print_json then
    Yojson.Safe.to_channel stdout (Ast.binary_format_to_yojson (Ast.current_version, files));

  (* Type-check all files, then perform a whole-program rewriting. *)
  Checker.check_everything files;
  let files = Simplify.simplify files in

  (* -dsimplify *)
  if !arg_print_simplify then
    print PrintAst.print_files files;
  Checker.check_everything files;

  (* Translate to C*, then to C. *)
  let files = AstToCStar.translate_files files in
  let headers = CStarToC.mk_headers files in
  let files = CStarToC.mk_files files in

  (* -dc *)
  if !arg_print_c then
    print PrintC.print_files files;

  flush stderr;
  Printf.printf "KreMLin: writing out .c and .h files for %s\n" (String.concat ", " (List.map fst files));
  Output.write_c files;
  Output.write_h headers;

  if !arg_skip_compilation then
    exit 0;
  let remaining_c_files = Driver.compile (List.map fst files) !c_files in

  if !arg_skip_linking then
    exit 0;
  Driver.link remaining_c_files !o_files
