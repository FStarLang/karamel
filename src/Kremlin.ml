(** KreMLin, a tool to translate from a minimal ML-like language to C. *)

let _ =
  let arg_print_ast = ref false in
  let arg_print_json = ref false in
  let arg_print_simplify = ref false in
  let arg_print_pattern = ref false in
  let arg_print_inline = ref false in
  let arg_print_c = ref false in
  let arg_print_check = ref 0 in
  let arg_skip_extraction = ref false in
  let arg_skip_compilation = ref false in
  let arg_skip_linking = ref false in
  let arg_verify = ref false in
  let arg_warn_error = ref "" in
  let arg_wasm = ref false in
  let c_files = ref [] in
  let o_files = ref [] in
  let fst_files = ref [] in
  let filename = ref "" in
  let usage = Printf.sprintf
{|KreMLin: from a ML-like subset to C

Usage: %s [OPTIONS] FILES

High-level description:
  1. If some FILES end with .fst, and [-verify] is set, KreMLin will call
     [fstar] on them to perform verification.
  2. If some FILES end with .fst, KreMLin will call [fstar] on them to perform
     extraction and produce [out.krml].
  3. If exactly one FILE ends with [.krml] or [.json], or if a [.krml] file was
     produced at step 2., KreMLin will generate a series of [.c] and [.h] files
     in the directory specified by [-tmpdir], or in the current directory.
  4. If some FILES end with [.c], KreMLin will compile them along with the [.c]
     files generated at step 3. to obtain a series of [.o] files.
  5. If some FILES end with [.o], KreMLin will link them along with the [.o] files
     obtained at step 4. to obtain a final executable.

The [-skip-extraction] option will stop KreMLin after step 1.
The [-skip-compilation] option will stop KreMLin after step 3.
The [-skip-linking] option will stop KreMLin after step 4.

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
  5: type definition contains an application of an undefined type abbreviation
  6: variable-length array

Supported options:|} Sys.argv.(0) !Options.warn_error
  in
  let found_file = ref false in
  let prepend r = fun s -> r := s :: !r in
  let spec = [
    (* KreMLin as a driver *)
    "-cc", Arg.Set_string Options.cc, " compiler to use; one of gcc (default), compcert, g++, clang";
    "-fsopt", Arg.String (prepend Options.fsopts), " option to pass to F*";
    "-ccopt", Arg.String (prepend Options.ccopts), " option to pass to the C compiler and linker";
    "-ldopt", Arg.String (prepend Options.ldopts), " option to pass to the C linker";
    "-skip-extraction", Arg.Set arg_skip_extraction, " stop after step 1.";
    "-skip-compilation", Arg.Set arg_skip_compilation, " stop after step 3.";
    "-skip-linking", Arg.Set arg_skip_linking, " stop after step 4.";
    "-verify", Arg.Set arg_verify, " ask F* to verify the program";
    "-verbose", Arg.Set Options.verbose, "  show the output of intermediary tools when acting as a driver for F* or the C compiler";
    "-wasm", Arg.Set arg_wasm, "  emit a .wasm file instead of C";
    "", Arg.Unit (fun _ -> ()), " ";

    (* Controling the behavior of KreMLin *)
    "-no-prefix", Arg.String (prepend Options.no_prefix), " don't prepend the module name to declarations from this module";
    "-add-include", Arg.String (prepend Options.add_include), " prepend #include the-argument to every generated file";
    "-tmpdir", Arg.Set_string Options.tmpdir, " temporary directory for .out, .c, .h and .o files";
    "-I", Arg.String (prepend Options.includes), " add directory to search path (F* and C compiler)";
    "-o", Arg.Set_string Options.exe_name, "  name of the resulting executable";
    "-drop", Arg.String (prepend Options.in_kremlib), "  do not extract this module (but keep it for its signature and types)";
    "-warn-error", Arg.Set_string arg_warn_error, "  decide which errors are fatal / warnings / silent (default: " ^ !Options.warn_error ^")";
    "", Arg.Unit (fun _ -> ()), " ";

    (* For developers *)
    "-djson", Arg.Set arg_print_json, " dump the input AST as JSON";
    "-dast", Arg.Set arg_print_ast, " pretty-print the internal AST";
    "-dcheck", Arg.Set_int arg_print_check, " N pretty-print the internal AST after Nth check";
    "-dpattern", Arg.Set arg_print_pattern, " pretty-print after pattern removal";
    "-dsimplify", Arg.Set arg_print_simplify, " pretty-print the internal AST after simplification";
    "-dinline", Arg.Set arg_print_inline, " pretty-print the internal AST after inlining";
    "-dc", Arg.Set arg_print_c, " pretty-print the output C";
    "", Arg.Unit (fun _ -> ()), " ";
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
      Driver.run_fstar !arg_verify !arg_skip_extraction !fst_files
    else
      !filename
  in

  let print f files =
    flush stdout;
    flush stderr;
    let open PPrint in
    Printf.printf "Read [%s]. Printing with w=%d\n" filename Utils.twidth;
    Print.print (f files ^^ hardline);
    flush stdout
  in

  let files = InputAst.read_file filename in

  (* -djson *)
  if !arg_print_json then
    Yojson.Safe.to_channel stdout (InputAst.binary_format_to_yojson (InputAst.current_version, files));

  (* -dast *)
  let files = Builtin.prims :: InputAstToAst.mk_files files in
  if !arg_print_ast then
    print PrintAst.print_files files;

  (* The first check can only occur after type abbreviations have been inlined,
   * and type abbreviations we don't know about have been replaced by TAny.
   * Otherwise, the checker is too stringent and will drop files. *)
  let l = List.length files in
  let files = DataTypes.drop_match_cast files in
  let files = Checker.check_everything files in
  if !arg_print_check = 1 then
    print PrintAst.print_files files;
  let files = Inlining.inline_type_abbrevs files in

  (* Make sure implementors that target Kremlin can tell apart their bugs vs.
   * mine *)
  flush stderr;
  if List.length files = l then
    KPrint.bprintf "%s✔%s Input file successfully checked\n" Ansi.green Ansi.reset
  else
    KPrint.bprintf "%s⚠%s Dropped some files while checking\n" Ansi.orange Ansi.reset;

  (* Simplify data types and remove patterns. *)
  let datatypes_state, files = DataTypes.everything files in
  if !arg_print_pattern then
    print PrintAst.print_files files;

  (* Perform a whole-program rewriting. *)
  let files = Checker.check_everything files in
  KPrint.bprintf "%s✔%s Pattern compilation successfully checked\n" Ansi.green Ansi.reset;
  if !arg_print_check = 2 then
    print PrintAst.print_files files;
  let files = Simplify.simplify1 files in
  let files = Simplify.simplify2 files in
  if !arg_print_simplify then
    print PrintAst.print_files files;

  (* The criterion for determining whether we should inline really works well
   * after everything has been simplified, but inlining requires a new round of
   * hoisting. *)
  let files = Inlining.inline_function_frames files in
  let files = Simplify.simplify2 files in
  if !arg_print_inline then
    print PrintAst.print_files files;

  let files = Checker.check_everything files in
  KPrint.bprintf "%s✔%s Simplifications successfully checked\n" Ansi.green Ansi.reset;
  (* Do this at the last minute because the checker still needs these type
   * abbreviations to check that our stuff makes sense. *)
  let files = Inlining.drop_type_abbrevs files in
  let files = Inlining.drop_unused files in

  (* This breaks typing. *)
  let files =
    if !Options.cc <> "compcert" then
      DataTypes.anonymous_unions datatypes_state files
    else
      files
  in

  (* Translate to C*... *)
  let files = AstToCStar.translate_files files in

  if !arg_wasm then
    (* ... then to Wasm *)
    let module_ = CStarToWasm.mk_module files in
    let s = Wasm.Encode.encode module_ in
    if !Options.exe_name = "" then
      Options.exe_name := "out.wasm";
    output_string (open_out !Options.exe_name) s;
    KPrint.bprintf "Wrote WASM output to %s\n" !Options.exe_name
  else
    (* ... then to C *)
    let headers = CStarToC.mk_headers files in
    let files = CStarToC.mk_files files in

    (* -dc *)
    if !arg_print_c then
      print PrintC.print_files files;

    flush stdout;
    flush stderr;
    Printf.printf "KreMLin: writing out .c and .h files for %s\n" (String.concat ", " (List.map fst files));
    let to_drop = List.map (String.map (function '.' -> '_' | x -> x)) !Options.in_kremlib in
    let files = List.filter (fun (name, _) ->
      not (List.exists ((=) name) to_drop)
    ) files in
    Output.write_c files;
    let headers = List.filter (fun (name, _) ->
      not (List.exists ((=) name) to_drop)
    ) headers in
    Output.write_h headers;

    if !arg_skip_compilation then
      exit 0;
    let remaining_c_files = Driver.compile (List.map fst files) !c_files in

    if !arg_skip_linking then
      exit 0;
    Driver.link remaining_c_files !o_files
