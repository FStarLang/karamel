(** KreMLin, a tool to translate from a minimal ML-like language to C. *)

let _ =
  let arg_print_ast = ref false in
  let arg_print_json = ref false in
  let arg_print_simplify = ref false in
  let arg_print_inline = ref false in
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

The [-warn-error] option follows the OCaml syntax, namely:
  - [r] is a range of warnings (either a number [n], or a range [n..n])
  - [-r] silences range [r]
  - [+r] enables range [r]
  - [@r] makes [r] fatal.

The default is %s and the available warnings are:
  1: not generating code for a provided file
  2: found a reference to a function without implementation
  3: external command failed
  4: type error / malformed input

Supported options:|} Sys.argv.(0) !Options.warn_error
  in
  let found_file = ref false in
  let prepend r = fun s -> r := s :: !r in
  let spec = [
    "-djson", Arg.Set arg_print_json, " dump the input AST as JSON";
    "-dast", Arg.Set arg_print_ast, " pretty-print the internal AST";
    "-dinline", Arg.Set arg_print_inline, " pretty-print the internal AST after inlining";
    "-dsimplify", Arg.Set arg_print_simplify, " pretty-print the internal AST after simplification";
    "-dc", Arg.Set arg_print_c, " pretty-print the output C";
    "-skip-compilation", Arg.Set arg_skip_compilation, " stop after step 2.";
    "-skip-linking", Arg.Set arg_skip_linking, " stop after step 3.";
    "-no-prefix", Arg.String (prepend Options.no_prefix), " don't prepend the module name to declarations from this module";
    "--lax", Arg.Set Options.lax, " forward --lax to F*";
    "-add-include", Arg.String (prepend Options.add_include), " prepend #include the-argument to the generated file";
    "-tmpdir", Arg.Set_string Options.tmpdir, " temporary directory for .out, .c, .h and .o files";
    "-I", Arg.String (prepend Options.includes), " add directory to search path (F* and C compiler)";
    "-o", Arg.Set_string Options.exe_name, "  name of the resulting executable";
    "-warn-error", Arg.Set_string arg_warn_error, "  decide which errors are fatal / warnings / silent (default: " ^ !Options.warn_error ^")";
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
    flush stdout;
    flush stderr;
    let open PPrint in
    Printf.printf "Read [%s]. Printing with w=%d\n" filename Utils.twidth;
    Print.print (f files ^^ hardline)
  in

  let files = InputAst.read_file filename in

  (* -djson *)
  if !arg_print_json then
    Yojson.Safe.to_channel stdout (InputAst.binary_format_to_yojson (InputAst.current_version, files));

  (* -dast *)
  let files = InputAstToAst.mk_files files in
  if !arg_print_ast then
    print PrintAst.print_files files;

  (* Perform a whole-program rewriting. *)
  let files = Checker.check_everything files in

  let files = Simplify.simplify files in
  if !arg_print_simplify then
    print PrintAst.print_files files;

  (* The criterion for determining whether we should inline really works well
   * after everything has been simplified, but inlining requires a new round of
   * hoisting. *)
  let files = Frames.inline_as_required files in
  let files = Simplify.simplify2 files in
  if !arg_print_inline then
    print PrintAst.print_files files;

  let files = Checker.check_everything files in

  (* Translate to C*, then to C. *)
  let files = AstToCStar.translate_files files in
  let headers = CStarToC.mk_headers files in
  let files = CStarToC.mk_files files in

  (* -dc *)
  if !arg_print_c then
    print PrintC.print_files files;

  flush stdout;
  flush stderr;
  Printf.printf "KreMLin: writing out .c and .h files for %s\n" (String.concat ", " (List.map fst files));
  let files = List.filter (fun (name, _) -> name <> "C") files in
  Output.write_c files;
  let headers = List.filter (fun (name, _) -> name <> "C") headers in
  Output.write_h headers;

  if !arg_skip_compilation then
    exit 0;
  let remaining_c_files = Driver.compile (List.map fst files) !c_files in

  if !arg_skip_linking then
    exit 0;
  Driver.link remaining_c_files !o_files
