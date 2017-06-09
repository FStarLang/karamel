(** KreMLin, a tool to translate from a minimal ML-like language to C. *)

module Time = struct
  let t = ref None

  let start () =
    t := Some (Unix.times ())

  let tick buf () =
    let t' = Unix.times () in
    let diff = t'.Unix.tms_cutime -. (Option.must !t).Unix.tms_cutime +.
      t'.Unix.tms_utime -. (Option.must !t).Unix.tms_utime
    in
    t := Some t';

    Printf.bprintf buf "⏱️ ";
    let rec smart_format whole f =
      if f < 1. && whole then
        Printf.bprintf buf "<1ms"
      else if f < 1000. then
        Printf.bprintf buf "%.0fms" f
      else if f < 60. *. 1000. then
        let seconds = floor (f /. 1000.) in
        Printf.bprintf buf "%.0fs and " seconds;
        smart_format false (f -. seconds *. 1000.)
      else if f < 3600. *. 1000. then
        let minutes = floor (f /. 60. *. 1000.) in
        Printf.bprintf buf "%.0fm" minutes;
        smart_format false (f -. minutes *. 60. *. 1000.)
      else
        let hours = floor (f /. 3_600_000.) in
        Printf.bprintf buf "%.0fh" hours;
        smart_format false (f -. hours *. 3_600_000.)
    in
    smart_format true (diff *. 1000.)
end

let _ =
  let arg_print_ast = ref false in
  let arg_print_json = ref false in
  let arg_print_simplify = ref false in
  let arg_print_pattern = ref false in
  let arg_print_inline = ref false in
  let arg_print_c = ref false in
  let arg_print_wasm = ref false in
  let arg_skip_extraction = ref false in
  let arg_skip_translation = ref false in
  let arg_skip_compilation = ref false in
  let arg_skip_linking = ref false in
  let arg_verify = ref false in
  let arg_warn_error = ref "" in
  let arg_wasm = ref false in
  let c_files = ref [] in
  let o_files = ref [] in
  let fst_files = ref [] in
  let filename = ref "" in
  let p k = String.concat " " (Array.to_list (List.assoc k (Options.default_options ()))) in
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
The [-skip-translation] option stops KreMLin after step 2.
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
    "-cc", Arg.Set_string Options.cc, " compiler to use; one of gcc (default), \
      compcert, g++, clang, msvc";
    "-m32", Arg.Set Options.m32, " turn on 32-bit cross-compiling";
    "-fsopt", Arg.String (prepend Options.fsopts), " option to pass to F* (use \
      -fsopts to pass a comma-separated list of values)";
    "-fsopts", Arg.String (csv (prepend Options.fsopts)), "";
    "-ccopt", Arg.String (prepend Options.ccopts), " option to pass to the C \
      compiler and linker (use -ccopts to pass a comma-separated list of values)";
    "-ccopts", Arg.String (csv (prepend Options.ccopts)), "";
    "-ldopt", Arg.String (prepend Options.ldopts), " option to pass to the C \
      linker (use -ldopts to pass a comma-separated list of values)";
    "-ldopts", Arg.String (csv (prepend Options.ldopts)), "";
    "-skip-extraction", Arg.Set arg_skip_extraction, " stop after step 1.";
    "-skip-translation", Arg.Set arg_skip_translation, " stop after step 2.";
    "-skip-compilation", Arg.Set arg_skip_compilation, " stop after step 3.";
    "-skip-linking", Arg.Set arg_skip_linking, " stop after step 4.";
    "-verify", Arg.Set arg_verify, " ask F* to verify the program";
    "-verbose", Arg.Set Options.verbose, "  show the output of intermediary \
      tools when acting as a driver for F* or the C compiler";
    "-wasm", Arg.Set arg_wasm, "  emit a .wasm file instead of C";
    "", Arg.Unit (fun _ -> ()), " ";

    (* Controlling the behavior of KreMLin *)
    "-no-prefix", Arg.String (prepend Options.no_prefix), " don't prepend the \
      module name to declarations from this module";
    "-bundle", Arg.String (fun s -> prepend Options.bundle (Bundles.parse s)), " \
      group modules into a single C translation unit (see above)";
    "-drop", Arg.String (fun s ->
      List.iter (prepend Options.drop) (Utils.parse Parser.drop s)),
      "  do not extract Code for this module (see above)";
    "-add-include", Arg.String (prepend Options.add_include), " prepend #include \
      the-argument to every generated file";
    "-header", Arg.String (fun f ->
      Options.header := Utils.file_get_contents f
    ), " prepend the contents of the given file at the beginning of each .c and .h";
    "-tmpdir", Arg.Set_string Options.tmpdir, " temporary directory for .out, \
      .c, .h and .o files";
    "-I", Arg.String (prepend Options.includes), " add directory to search path \
      (F* and C compiler)";
    "-o", Arg.Set_string Options.exe_name, "  name of the resulting executable";
    "-warn-error", Arg.Set_string arg_warn_error, "  decide which errors are \
      fatal / warnings / silent (default: " ^ !Options.warn_error ^")";
    "-fnostruct-passing", Arg.Clear Options.struct_passing, "  disable passing \
      structures by value and use pointers instead";
    "-fnoanonymous-unions", Arg.Clear Options.anonymous_unions, "  disable C11 \
      anonymous unions";
    "-fnouint128", Arg.Clear Options.uint128, "  don't assume a built-in type \
      __uint128";
    "-funroll-loops", Arg.Set_int Options.unroll_loops, "  textually expand \
      loops smaller than N";
    "-fparentheses", Arg.Set Options.parentheses, "  add unnecessary parentheses \
      to silence GCC and Clang's -Wparentheses";
    "", Arg.Unit (fun _ -> ()), " ";

    (* For developers *)
    "-djson", Arg.Set arg_print_json, " dump the input AST as JSON";
    "-dast", Arg.Set arg_print_ast, " pretty-print the internal AST";
    "-dpattern", Arg.Set arg_print_pattern, " pretty-print after pattern \
      removal";
    "-dsimplify", Arg.Set arg_print_simplify, " pretty-print the internal AST \
      after simplification";
    "-dinline", Arg.Set arg_print_inline, " pretty-print the internal AST after \
      inlining";
    "-dc", Arg.Set arg_print_c, " pretty-print the output C";
    "-dwasm", Arg.Set arg_print_wasm, " pretty-print the output Wasm";
    "-d", Arg.String (csv (prepend Options.debug_modules)), " debug the specific \
      comma-separated list of values; currently supported: \
      inline,bundle,wasm-calls,force-c";
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
    (Array.append [| Sys.argv.(0) |] (List.assoc !Options.cc (Options.default_options ())))
    spec anon_fun usage;

  (* Then refine that based on the user's preferences. *)
  if !arg_warn_error <> "" then
    Warnings.parse_warn_error !arg_warn_error;

  if !arg_wasm then begin
    Options.uint128 := false;
    Options.anonymous_unions := false;
    Options.struct_passing := false
  end;

  (* Timings. *)
  Time.start ();
  let tick_print ok fmt =
    flush stdout;
    flush stderr;
    if ok then
      Printf.printf ("%s✔%s [" ^^ fmt) Ansi.green Ansi.reset
    else
      Printf.printf ("%s⚠%s [" ^^ fmt) Ansi.red Ansi.reset;
    KPrint.bprintf "] %a\n" Time.tick ()
  in


  (* Shall we run F* first? *)
  let filename =
    if List.length !fst_files > 0 then
      let f = Driver.run_fstar !arg_verify !arg_skip_extraction !arg_skip_translation !fst_files in
      tick_print true "F*";
      f
    else
      !filename
  in

  (* Dumping the AST for debugging purposes *)
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
  let files = Builtin.prelude @ InputAstToAst.mk_files files in
  if !arg_print_ast then
    print PrintAst.print_files files;

  (* 1. Minimal cleanup, remove higher-order combinators (e.g. map) with mere
   * calls to the base [for] combinator. These combinators (e.g. map) are
   * polymorphic; by inlining them, we make sure they can be type-checked
   * monorphically at call-site. We then remove the polymorphic definitions
   * (e.g. map) as we don't know how to type-check them. Finally, perform a
   * first round of type-checking. If things fail at this stage, most likely not
   * our fault (bad input?). *)
  let files = DataTypes.drop_match_cast files in
  let files = Inlining.inline_combinators files in
  let files = Inlining.drop_polymorphic_functions files in
  let has_errors, files = Checker.check_everything ~warn:true files in
  tick_print (not has_errors) "Checking input file";

  (* 2. Perform bundling early, as later analyses need to know which functions
   * are in the same file and which are not. *)
  let files = Bundles.make_bundles files in
  let files = Inlining.inline_type_abbrevs files in
  let has_errors, files = Checker.check_everything files in
  tick_print (not has_errors) "Bundle + inline types";

  (* 3. Compile data types and pattern matches to enums, structs, switches and
   * if-then-elses. *)
  let datatypes_state, files = DataTypes.everything files in
  if !arg_print_pattern then
    print PrintAst.print_files files;
  let has_errors, files = Checker.check_everything files in
  tick_print (not has_errors) "Pattern matches compilation";

  (* 4. First round of simplifications. *)
  let files = if !arg_wasm then SimplifyWasm.simplify files else files in
  let files = Simplify.simplify1 files in
  let files = Simplify.simplify2 files in
  if !arg_print_simplify then
    print PrintAst.print_files files;
  let has_errors, files = Checker.check_everything files in
  tick_print (not has_errors) "Simplify 1+2";

  (* 5. Whole-program transformations. Inline functions marked as [@substitute]
   * or [StackInline] into their parent's bodies. This is a whole-program
   * dataflow analysis done using a fixpoint computation. If needed, pass
   * structures by reference, and also allocate all structures in memory. This
   * creates new opportunities for the removal of unused variables, but also
   * breaks the earlier transformation to a statement language, which we perform
   * again. Note that [remove_unused] generates MetaSequence let-bindings,
   * meaning that it has to occur before [simplify2]. *)
  let files = Inlining.inline_function_frames files in
  let files = if not !Options.struct_passing then Structs.pass_by_ref files else files in
  let files = if !arg_wasm then Structs.in_memory files else files in
  let files = Simplify.remove_unused files in
  let files = Simplify.simplify2 files in
  let has_errors, files = Checker.check_everything files in
  if !arg_print_inline then
    print PrintAst.print_files files;
  tick_print (not has_errors) "Inline + Simplify 2";

  (* 6. Some transformations that break typing: remove type application
   * definitions (creates unbound types), drop unused functions (note: this
   * needs to happen after [inline_function_frames], as this pass removes
   * illegal Private flags), enable anonymous unions for syntactic elegance. *)
  let files = Inlining.drop_type_applications files in
  let files = Inlining.drop_unused files in
  let files =
    if !Options.anonymous_unions then
      DataTypes.anonymous_unions datatypes_state files
    else
      files
  in

  (* 7. Drop both files and selected declarations within some files, as a [-drop
   * Foo -bundle Bar=Foo] command-line requires us to go inside file [Bar] to
   * drop the declarations that originate from [Foo]. *)
  let drop l =
    let l = List.filter (fun (name, _) -> not (Drop.file name)) l in
    Ast.filter_decls (fun d ->
      if Drop.lid (Ast.lid_of_decl d) then
        None
      else
        Some d
    ) l
  in
  let files = drop files in
  tick_print true "Drop";

  (* 8. Final transformation on the AST: go to C names. This must really be done
   * at the last minute, since it invalidates pretty much any map ever built. *)
  let files = Simplify.to_c_names files in

  if !arg_wasm && not (Options.debug "force-c") then
    (* The Wasm backend diverges here. We go to [CFlat] (an expression
     * language), then directly into the Wasm AST. *)
    let files = AstToCFlat.mk_files files in
    tick_print true "AstToCFlat";

    let modules = CFlatToWasm.mk_files files in
    tick_print true "CFlatToWasm";

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
    tick_print true "AstToCStar";

    (* ... then to C *)
    let headers = CStarToC.mk_headers files in
    let files = CStarToC.mk_files files in
    tick_print true "CStarToC";

    (* -dc *)
    if !arg_print_c then
      print PrintC.print_files files;

    flush stdout;
    flush stderr;
    Output.write_c files;
    Output.write_h headers;
    tick_print true "PrettyPrinting";

    Printf.printf "KreMLin: wrote out .c and .h files for %s\n" (String.concat ", " (List.map fst files));

    if !arg_skip_compilation then
      exit 0;
    let remaining_c_files = Driver.compile (List.map fst files) !c_files in

    if !arg_skip_linking then
      exit 0;
    Driver.link remaining_c_files !o_files
