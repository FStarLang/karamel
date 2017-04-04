(** KreMLin, a tool to translate from a minimal ML-like language to C. *)

let _ =
  let arg_print_ast = ref false in
  let arg_print_json = ref false in
  let arg_print_simplify = ref false in
  let arg_print_pattern = ref false in
  let arg_print_inline = ref false in
  let arg_print_c = ref false in
  let arg_print_wasm = ref false in
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
  let p k = String.concat " " (Array.to_list (List.assoc k Options.default_options)) in
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
  5. If some FILES end with [.o], [.S] or [.a], KreMLin will link them along with the
     [.o] files obtained at step 4. to obtain a final executable.

The [-skip-extraction] option stops KreMLin after step 1.
The [-skip-compilation] option stops KreMLin after step 3.
The [-skip-linking] option stops KreMLin after step 4.

The [-warn-error] option follows the OCaml syntax, namely:
  - [r] is a range of warnings (either a number [n], or a range [n..n])
  - [-r] silences range [r]
  - [+r] enables range [r]
  - [@r] makes range [r] fatal.

The default is %s and the available warnings are:
  1: not generating code for a provided file
  2: found a reference to a function without implementation
  3: external command failed
  4: type error / malformed input
  5: type definition contains an application of an undefined type abbreviation
  6: variable-length array
  7: private F* function cannot be marked as C static
  8: C inline function reference across translation units

The [-bundle] option takes an argument of the form Api=Pattern1,...,Patternn
where the Api= part is optional and a pattern is either Foo.Bar (exact match) or
Foo.Baz.* (prefix). The semantics are as follows: all the modules that match a
pattern are grouped into a single C translation unit, and their declarations are
marked as static, inasmuch as cross-translation unit calls permit. If the Api=
part is present, then the module named Api must be found within the
set of input files, and its declarations are appended to the translation unit
without any visibility modifications.

The [-drop] option take a Pattern argument and skips code generation for the
modules that match the pattern.

The default arguments are: %s

All include directories and paths supports two special prefixes:
  - if a path starts with FSTAR_LIB, this will expand to wherever F*'s ulib
    directory is
  - if a path starts with FSTAR_HOME, this will expand to wherever the source
    checkout of F* is (this does not always exist, e.g. in the case of an OPAM
    setup).

The compiler switches turn on the following options.
  [-cc gcc] (default) adds [%s]
  [-cc clang] adds [%s]
  [-cc g++] adds [%s]
  [-cc msvc] adds [%s]
  [-cc compcert] adds [%s]

Supported options:|}
    Sys.argv.(0)
    !Options.warn_error
    (String.concat " " (KList.map_flatten (fun b ->
      [ "-bundle"; Bundle.string_of_bundle b ]
    ) !Options.bundle @ KList.map_flatten (fun p ->
      [ "-drop"; Bundle.string_of_pat p ]
    ) !Options.drop))
    (p "gcc")
    (p "clang")
    (p "g++")
    (p "msvc")
    (p "compcert")
  in
  let found_file = ref false in
  let prepend r = fun s -> r := s :: !r in
  let csv f s =
    List.iter f (KString.split_on_char ',' s)
  in
  let spec = [
    (* KreMLin as a driver *)
    "-cc", Arg.Set_string Options.cc, " compiler to use; one of gcc (default), compcert, g++, clang, msvc";
    "-m32", Arg.Set Options.m32, " turn on 32-bit cross-compiling";
    "-fsopt", Arg.String (prepend Options.fsopts), " option to pass to F* (use -fsopts to pass a comma-separated list of values)";
    "-fsopts", Arg.String (csv (prepend Options.fsopts)), "";
    "-ccopt", Arg.String (prepend Options.ccopts), " option to pass to the C compiler and linker (use -ccopts to pass a comma-separated list of values)";
    "-ccopts", Arg.String (csv (prepend Options.ccopts)), "";
    "-ldopt", Arg.String (prepend Options.ldopts), " option to pass to the C linker (use -ldopts to pass a comma-separated list of values)";
    "-ldopts", Arg.String (csv (prepend Options.ldopts)), "";
    "-skip-extraction", Arg.Set arg_skip_extraction, " stop after step 1.";
    "-skip-compilation", Arg.Set arg_skip_compilation, " stop after step 3.";
    "-skip-linking", Arg.Set arg_skip_linking, " stop after step 4.";
    "-verify", Arg.Set arg_verify, " ask F* to verify the program";
    "-verbose", Arg.Set Options.verbose, "  show the output of intermediary tools when acting as a driver for F* or the C compiler";
    "-wasm", Arg.Set arg_wasm, "  emit a .wasm file instead of C";
    "", Arg.Unit (fun _ -> ()), " ";

    (* Controlling the behavior of KreMLin *)
    "-no-prefix", Arg.String (prepend Options.no_prefix), " don't prepend the module name to declarations from this module";
    "-bundle", Arg.String (fun s -> prepend Options.bundle (Bundles.parse s)), " group modules into a single C translation unit (see above)";
    "-drop", Arg.String (fun s -> prepend Options.drop (Utils.parse Parser.drop s)), "  do not extract Code for this module (see above)";
    "-add-include", Arg.String (prepend Options.add_include), " prepend #include the-argument to every generated file";
    "-tmpdir", Arg.Set_string Options.tmpdir, " temporary directory for .out, .c, .h and .o files";
    "-I", Arg.String (prepend Options.includes), " add directory to search path (F* and C compiler)";
    "-o", Arg.Set_string Options.exe_name, "  name of the resulting executable";
    "-warn-error", Arg.Set_string arg_warn_error, "  decide which errors are fatal / warnings / silent (default: " ^ !Options.warn_error ^")";
    "-fnostruct-passing", Arg.Clear Options.struct_passing, "  disable passing structures by value and use pointers instead";
    "-fnoanonymous-unions", Arg.Clear Options.anonymous_unions, "  disable C11 anonymous unions";
    "-fnouint128", Arg.Clear Options.uint128, "  don't assume a built-in type __uint128";
    "", Arg.Unit (fun _ -> ()), " ";

    (* For developers *)
    "-djson", Arg.Set arg_print_json, " dump the input AST as JSON";
    "-dast", Arg.Set arg_print_ast, " pretty-print the internal AST";
    "-dpattern", Arg.Set arg_print_pattern, " pretty-print after pattern removal";
    "-dsimplify", Arg.Set arg_print_simplify, " pretty-print the internal AST after simplification";
    "-dinline", Arg.Set arg_print_inline, " pretty-print the internal AST after inlining";
    "-dc", Arg.Set arg_print_c, " pretty-print the output C";
    "-dwasm", Arg.Set arg_print_wasm, " pretty-print the output Wasm";
    "-d", Arg.String (csv (prepend Options.debug_modules)), " debug the specific comma-separated list of values; currently supported: inline,bundle,wasm-calls";
    "", Arg.Unit (fun _ -> ()), " ";
  ] in
  let spec = Arg.align spec in
  let anon_fun f =
    if Filename.check_suffix f ".fst" then
      fst_files := f :: !fst_files
    else if List.exists (Filename.check_suffix f) [ ".o"; ".S"; ".a" ] then
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
  in
  Arg.parse spec anon_fun usage;

  if not !found_file ||
     List.length !fst_files = 0 && !filename = "" ||
     List.length !fst_files > 0 && !filename <> ""
  then begin
    print_endline (Arg.usage_string spec usage);
    exit 1
  end;

  (* First enable the default warn-error string. *)
  Warnings.parse_warn_error !Options.warn_error;

  (* Then, bring in the "default options" for each compiler. *)
  Arg.parse_argv ~current:(ref 0)
    (Array.append [| Sys.argv.(0) |] (List.assoc !Options.cc Options.default_options))
    spec anon_fun usage;

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
  let files = DataTypes.drop_match_cast files in
  let files = Inlining.inline_combinators files in
  let files = Inlining.drop_polymorphic_functions files in
  let has_errors, files = Checker.check_everything ~warn:true files in

  (* Make sure implementors that target Kremlin can tell apart their bugs vs.
   * mine *)
  flush stderr;
  if not has_errors then
    KPrint.bprintf "%s✔%s Input file successfully checked\n" Ansi.green Ansi.reset
  else
    KPrint.bprintf "%s⚠%s Dropped some declarations while checking\n" Ansi.orange Ansi.reset;
  flush stdout;

  let files = Bundles.make_bundles files in
  let _, files = Checker.check_everything files in

  let files = Inlining.inline_type_abbrevs files in

  (* Simplify data types and remove patterns. *)
  let datatypes_state, files = DataTypes.everything files in
  if !arg_print_pattern then
    print PrintAst.print_files files;

  (* Perform a whole-program rewriting. *)
  let _, files = Checker.check_everything files in
  KPrint.bprintf "%s✔%s Pattern compilation successfully checked\n" Ansi.green Ansi.reset;

  let files = if !arg_wasm then Simplify.simplify_wasm files else files in
  let files = Simplify.simplify1 files in
  let files = Simplify.simplify2 files in
  if !arg_print_simplify then
    print PrintAst.print_files files;

  (* The criterion for determining whether we should inline really works well
   * after everything has been simplified, but inlining requires a new round of
   * hoisting. *)
  let files = Inlining.inline_function_frames files in
  let files = if not !Options.struct_passing then Structs.rewrite files else files in
  let files = Simplify.simplify2 files in
  if !arg_print_inline then
    print PrintAst.print_files files;

  let _, files = Checker.check_everything files in
  KPrint.bprintf "%s✔%s Simplify + inlining successfully checked\n" Ansi.green Ansi.reset;
  (* Do this at the last minute because the checker still needs these type
   * abbreviations to check that our stuff makes sense. *)
  let files = Inlining.drop_type_applications files in
  (* This must happen AFTER inline_function_frames has removed some illegal
   * private flags. Otherwise, we may be removing too many things. *)
  let files = Inlining.drop_unused files in

  (* This breaks typing. *)
  let files =
    if !Options.anonymous_unions then
      DataTypes.anonymous_unions datatypes_state files
    else
      files
  in

  (* Drop files (e.g. -drop FStar.Heap) *)
  let drop l =
    let should_drop name =
      List.exists (fun p -> Bundles.pattern_matches p name) !Options.drop
    in
    let l = List.filter (fun (name, _) -> not (should_drop name)) l in
    (* Note that after bundling, we need to go inside bundles to find top-level
     * names that originate from a module we were meant to drop, and drop
     * individual declarations. *)
    Ast.filter_decls (fun d ->
      let f = String.concat "_" (fst (Ast.lid_of_decl d)) in
      if should_drop f then
        None
      else
        Some d
    ) l
  in
  let files = drop files in

  (* The "drop files" pass above needs some properly-built names... do this at
   * the last minute, really. *)
  let files = Simplify.to_c_names files in

  if !arg_wasm then
    (* ... then to Wasm *)
    let files = AstToCFlat.mk_files files in
    let modules = CFlatToWasm.mk_files files in
    List.iter (fun (name, module_) ->
      let s = Wasm.Encode.encode module_ in
      let name = name ^ ".wasm" in
      Utils.with_open_out (Filename.concat !Options.tmpdir name) (fun oc -> output_string oc s);
      KPrint.bprintf "Wrote %s\n" name;
      if !arg_print_wasm then
        Wasm.Print.module_ stdout Utils.twidth module_;
      flush stderr
    ) modules

  else
    (* Translate to C*... *)
    let files = AstToCStar.mk_files files in

    (* ... then to C *)
    let headers = CStarToC.mk_headers files in
    let files = CStarToC.mk_files files in

    (* -dc *)
    if !arg_print_c then
      print PrintC.print_files files;

    flush stdout;
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
