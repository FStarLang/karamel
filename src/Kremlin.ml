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
  let arg_print_monomorphization = ref false in
  let arg_print_structs = ref false in
  let arg_print_c = ref false in
  let arg_print_wasm = ref false in
  let arg_skip_extraction = ref false in
  let arg_skip_translation = ref false in
  let arg_skip_compilation = ref false in
  let arg_skip_linking = ref false in
  let arg_verify = ref false in
  let arg_warn_error = ref "" in
  let arg_c89 = ref false in
  let c_files = ref [] in
  let o_files = ref [] in
  let js_files = ref [] in
  let fst_files = ref [] in
  let filenames = ref [] in
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
  9: need to manually call static initializers for globals
  10: deprecated feature
  11: subexpression is not Low*; cannot proceed
  12: cannot be compiled to Wasm

The [-bundle] option takes an argument of the form Api=Pattern1,...,Patternn
where the Api= part is optional and a pattern is either Foo.Bar (exact match) or
Foo.Baz.* (prefix). The semantics are as follows: all the modules that match a
pattern are grouped into a single C translation unit, and their declarations are
marked as static, inasmuch as cross-translation unit calls permit. If the Api=
part is present, then the module named Api must be found within the
set of input files, and its declarations are appended to the translation unit
without any visibility modifications.

The default arguments are: %s

All include directories and paths supports special prefixes:
  - if a path starts with FSTAR_LIB, this will expand to wherever F*'s ulib
    directory is
  - if a path starts with FSTAR_HOME, this will expand to wherever the source
    checkout of F* is (this does not always exist, e.g. in the case of an OPAM
    setup)
  - if a path starts with KRML_HOME, this will expand to wherever the source
    checkout of KreMLin is

The compiler switches turn on the following options.
  [-cc gcc] (default) adds [%s]
  [-cc clang] adds [%s]
  [-cc g++] adds [%s]
  [-cc msvc] adds [%s]
  [-cc compcert] adds [%s]

The [-fc89] option triggers [-fnouint128], [-fnoanonymous-unions],
[-fnocompound-literals] and [-fc89-scope]. It also changes the invocations above
to use [-std=c89].

To debug Wasm codegen, it might be useful to trigger the same compilation path
as Wasm, but emit C code instead. This can be achieved with [-wasm -d
force-c,c-calls,wasm-calls -drop C,TestLib -add-include '"hack.h"' -fnouint128]
where [hack.h] contains [#define WasmSupport_check_buffer_size(X)].

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
  let used_drop = ref false in
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
    "-wasm", Arg.Set Options.wasm, "  emit a .wasm file instead of C";
    "", Arg.Unit (fun _ -> ()), " ";

    (* Controlling the behavior of KreMLin *)
    "-add-early-include", Arg.String (prepend Options.add_early_include),
      "prepend #include the-argument to every generated file, before kremlib.h";
    "-add-include", Arg.String (prepend Options.add_include), " prepend #include \
      the-argument to every generated file, after the #define __FOO_H";
    "-minimal", Arg.Set Options.minimal, "do not prepend #include \"kremlib.h\"; do \
      not bundle FStar";
    "-static-header", Arg.String (prepend Options.static_header), " generate a \
      .h for the given module where all functions are marked a static inline";
    "-no-prefix", Arg.String (prepend Options.no_prefix), " don't prepend the \
      module name to declarations from this module";
    "-bundle", Arg.String (fun s -> prepend Options.bundle (Bundles.parse s)), " \
      group modules into a single C translation unit (see above)";
    "-drop", Arg.String (fun s ->
      used_drop := true;
      List.iter (prepend Options.drop) (Utils.parse Parser.drop s)),
      "  do not extract Code for this module (see above)";
    "-header", Arg.String (fun f ->
      let c = Utils.file_get_contents f in
      Options.header := fun _ _ -> c
    ), " prepend the contents of the given file at the beginning of each .c and .h";
    "-tmpdir", Arg.Set_string Options.tmpdir, " temporary directory for .out, \
      .c, .h and .o files";
    "-I", Arg.String (prepend Options.includes), " add directory to search path \
      (F* and C compiler)";
    "-o", Arg.Set_string Options.exe_name, "  name of the resulting executable";
    "-warn-error", Arg.String (fun s -> arg_warn_error := !arg_warn_error ^ s), "  decide which errors are \
      fatal / warnings / silent (default: " ^ !Options.warn_error ^")";

    (* Fine-tuning code generation. *)
    "", Arg.Unit (fun _ -> ()), " ";
    "-falloca", Arg.Set Options.alloca_if_vla, "  use alloca(3) for \
      variable-length arrays on the stack";
    "-fnostruct-passing", Arg.Clear Options.struct_passing, "  disable passing \
      structures by value and use pointers instead";
    "-fnoanonymous-unions", Arg.Clear Options.anonymous_unions, "  disable C11 \
      anonymous unions";
    "-fnouint128", Arg.Clear Options.uint128, "  don't assume a built-in type \
      __uint128";
    "-fnocompound-literals", Arg.Unit (fun () -> Options.compound_literals := `Never),
      "  don't generate C11 compound literals";
    "-funroll-loops", Arg.Set_int Options.unroll_loops, "  textually expand \
      loops smaller than N";
    "-fparentheses", Arg.Set Options.parentheses, "  add unnecessary parentheses \
      to silence GCC and Clang's -Wparentheses";
    "-fcurly-braces", Arg.Set Options.curly_braces, "  always add curly braces \
      around blocks";
    "-fc89-scope", Arg.Set Options.c89_scope, "  use C89 scoping rules";
    "-fc89", Arg.Set arg_c89, "  generate C89-compatible code (meta-option, see above)";
    "", Arg.Unit (fun _ -> ()), " ";

    (* For developers *)
    "-djson", Arg.Set arg_print_json, " dump the input AST as JSON";
    "-dast", Arg.Set arg_print_ast, " pretty-print the internal AST";
    "-dmonomorphization", Arg.Set arg_print_monomorphization, " pretty-print the \
      internal AST after monomorphization";
    "-dinline", Arg.Set arg_print_inline, " pretty-print the internal AST after \
      inlining";
    "-dpattern", Arg.Set arg_print_pattern, " pretty-print after pattern \
      matches compilation";
    "-dsimplify", Arg.Set arg_print_simplify, " pretty-print the internal AST \
      after going to a statement language";
    "-dstructs", Arg.Set arg_print_structs, " pretty-print the internal AST after \
      struct transformations";
    "-dc", Arg.Set arg_print_c, " pretty-print the output C";
    "-dwasm", Arg.Set arg_print_wasm, " pretty-print the output Wasm";
    "-d", Arg.String (csv (prepend Options.debug_modules)), " debug the specific \
      comma-separated list of values; currently supported: \
      inline,bundle,reachability,c-calls,wasm-calls,wasm-memory,wasm,force-c,cflat";
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
    else if Filename.check_suffix f ".js" then
      js_files := f :: !js_files
    else if Filename.check_suffix f ".json" || Filename.check_suffix f ".krml" then begin
      filenames := f :: !filenames
    end else
      Warnings.fatal_error "Unknown file extension for %s\n" f;
    found_file := true
  in
  Arg.parse spec anon_fun usage;

  if not !found_file ||
     List.length !fst_files = 0 && List.length !filenames = 0 ||
     List.length !fst_files > 0 && List.length !filenames > 0
  then begin
    print_endline (Arg.usage_string spec usage);
    exit 1
  end;

  (* First enable the default warn-error string. *)
  Warnings.parse_warn_error !Options.warn_error;

  (* Meta-options that enable other options. Do this now because it influences
   * the default options for each compiler. *)
  if !Options.wasm then begin
    Options.uint128 := false;
    Options.anonymous_unions := false;
    (* This forces the evaluation of compound literals to happen first, before
     * they are assigned. This is the C semantics, and the C compiler will do it
     * for us, so this is not generally necessary. *)
    Options.compound_literals := `Wasm;
    Options.struct_passing := false
  end;

  (* An actual C compilation wants to drop these two. *)
  if not !Options.wasm || Options.debug "force-c" then
    Options.drop := [
      Bundle.Module [ "FStar"; "Int"; "Cast"; "Full" ];
      Bundle.Module [ "C" ];
      Bundle.Module [ "TestLib" ]
    ] @ !Options.drop;

  (* Self-help. *)
  if !Options.wasm && Options.debug "force-c" then begin
    Options.add_include := "\"wasm-stubs.h\"" :: !Options.add_include;
    Options.drop := Bundle.Module [ "WasmSupport" ] :: !Options.drop
  end;

  if not !Options.minimal then
    Options.bundle :=
      ([], [ Bundle.Module [ "C"; "Loops" ]; Bundle.Module [ "Spec"; "Loops" ] ]) ::
      ([], [ Bundle.Prefix [ "FStar" ] ]) ::
      !Options.bundle;

  if !arg_c89 then begin
    Options.uint128 := false;
    Options.anonymous_unions := false;
    Options.compound_literals := `Never;
    Options.c89_scope := true;
    Options.c89_std := true
  end;

  (* Then, bring in the "default options" for each compiler. *)
  Arg.parse_argv ~current:(ref 0)
    (Array.append [| Sys.argv.(0) |] (List.assoc !Options.cc (Options.default_options ())))
    spec anon_fun usage;

  (* Then refine that based on the user's preferences. *)
  if !arg_warn_error <> "" then
    Warnings.parse_warn_error !arg_warn_error;

  if !used_drop then
    Warnings.(maybe_fatal_error ("", Deprecated ("-drop", "use a combination of \
      -bundle and -d reachability to make sure the functions are eliminated as \
      you wish")));

  (* If the compiler supports uint128, then we just drop the module and let
   * dependency analysis use FStar.UInt128.fsti. If the compiler does not,
   * then we bring the implementation into scope instead. The latter is
   * performed in src/Driver.ml because we need to know where FSTAR_HOME is. *)
  if !Options.uint128 then
    Options.drop := Bundle.Module [ "FStar"; "UInt128" ] :: !Options.drop;

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
  let filenames =
    if List.length !fst_files > 0 then
      (* Monolithic extraction, generates a single out.krml *)
      let f = Driver.run_fstar !arg_verify !arg_skip_extraction !arg_skip_translation !fst_files in
      tick_print true "F*";
      [ f ]
    else
      !filenames
  in

  (* Dumping the AST for debugging purposes *)
  let print f files =
    flush stdout;
    flush stderr;
    let open PPrint in
    let filenames = String.concat ", " filenames in
    Printf.printf "Read [%s]. Printing with w=%d\n" filenames Utils.twidth;
    Print.print (f files ^^ hardline);
    flush stdout
  in

  let files = InputAst.read_files filenames in

  (* These are modules we don't want because there's primitive support for them
   * in kremlin. *)
  let should_keep (name, _) = match name with
    | "FStar_Int8" | "FStar_UInt8" | "FStar_Int16" | "FStar_UInt16"
    | "FStar_Int31" | "FStar_UInt31" | "FStar_Int32" | "FStar_UInt32"
    | "FStar_Int63" | "FStar_UInt63" | "FStar_Int64" | "FStar_UInt64"
    | "FStar_Int128" | "FStar_HyperStack_ST" | "FStar_Monotonic_HyperHeap"
    | "FStar_Buffer" | "FStar_Monotonic_HyperStack" | "FStar_Monotonic_Heap"
    | "C_String" ->
        false
    | "FStar_UInt128" ->
        (* Keep if we don't use the uint128 type. *)
        not !Options.uint128
    | "WasmSupport" ->
        (* Keep if we're compiling to Wasm. *)
        !Options.wasm
    | _ ->
        true
  in
  let files = List.filter should_keep files in

  (* A quick sanity check to save myself some time. *)
  begin try
    let has_uint128 =
      List.exists (function
        | InputAst.DTypeFlat (([ "FStar"; "UInt128" ], "uint128"), _, _, _) ->
            true
        | _ ->
            false
      ) (List.assoc "FStar_UInt128" files)
    in
    (* The input file defines uint128 if and only if the backend does not
     * support it. *)
    if has_uint128 <> not !Options.uint128 then
      Warnings.fatal_error "The implementation of FStar.UInt128 should be \
        present in the input when using -fnouint128."
  with Not_found ->
    ()
  end;

  (* -djson *)
  if !arg_print_json then
    Yojson.Safe.to_channel stdout (InputAst.binary_format_to_yojson (InputAst.current_version, files));

  (* -dast *)
  let files = Builtin.prelude () @ Builtin.augment (InputAstToAst.mk_files files) in
  if !arg_print_ast then
    print PrintAst.print_files files;

  (* 0. Since the user may now pass several .krml files in an arbitrary order,
   * we need a topological order. Example:
   * - B.g depends on A.f and they both bundled (and private)
   * - A needs to come before B so that in the resulting bundle, "static void
   *   A_f" comes before "static void B_g" (since they're static, there's no
   *   forward declaration in the header. *)
  let files = Bundles.topological_sort files in

  (* 1. We create bundles, and monomorphize functions first. This creates more
   * applications of parameterized types, which we make sure are in the AST by
   * checking it. Note that bundling calls [drop_unused] already to do a first
   * round of unused code elimination! *)
  let files = Bundles.make_bundles files in
  (* This needs to happen before type monomorphization, so that list<t> and
   * list<t'> don't generate two distinct declarations (e.g. list__t and
   * list__t'). Also needs to happen before monomorphization of equalities. *)
  let files = Inlining.inline_type_abbrevs files in
  let files = DataTypes.remove_unused_type_arguments files in
  let files = Monomorphization.functions files in
  if !arg_print_monomorphization then
    print PrintAst.print_files files;
  let has_errors, files = Checker.check_everything ~warn:true files in
  tick_print (not has_errors) "Monomorphization";

  (* 2. We schedule phases that may create tuples. At this stage, all the
   * occurrences of parameterized data types are in the AST: we monomorphize
   * them too. Next, we inline function definitions according to [@substitute]
   * or [StackInline].  This once again changes the call graph but does not add
   * new instances. At this stage, some functions must lose their [Private]
   * qualifiers since the previous phases may have generated calls across module
   * boundaries. Once [private] qualifiers are stable, we can perform our
   * reachability analysis starting from the public functions of each module or
   * bundle. *)
  let files = Simplify.simplify0 files in
  (* Remove trivial matches now because they eliminate code that would generate
   * spurious dependencies otherwise. JP: TODO: fix F\*'s extraction instead! *)
  let files = DataTypes.simplify files in
  let files = Monomorphization.datatypes files in
  let files = Monomorphization.equalities files in
  let files = Inlining.inline files in
  let files = Inlining.drop_unused files in
  if !arg_print_inline then
    print PrintAst.print_files files;
  let has_errors, files = Checker.check_everything files in
  tick_print (not has_errors) "Inlining";

  (* 3. Compile data types and pattern matches to enums, structs, switches and
   * if-then-elses. Better have monomorphized functions first! *)
  let files = GcTypes.heap_allocate_gc_types files in
  (* JP: this phase has many maps that take lids as keys and does not have logic
   * to expand type abbreviations. TODO: remove [inline_type_abbrevs] and let
   * them be monomorphized just like the rest. Note: this phase re-inserts some
   * type abbreviations. *)
  let datatypes_state, files = DataTypes.everything files in
  if !arg_print_pattern then
    print PrintAst.print_files files;
  if Options.debug "types-depth" then
    Msvc.types_depth files;
  let has_errors, files = Checker.check_everything files in
  tick_print (not has_errors) "Pattern matches compilation";

  (* 4. Going to a statement language. JP: is this necessary? *)
  let files = Simplify.simplify2 files in
  if !arg_print_simplify then
    print PrintAst.print_files files;
  let has_errors, files = Checker.check_everything files in
  tick_print (not has_errors) "Simplify 2";

  (* 5. Whole-program transformations. If needed, pass structures by reference,
   * and also allocate all structures in memory. This creates new opportunities
   * for the removal of unused variables, but also breaks the earlier
   * transformation to a statement language, which we perform again. Note that
   * [remove_unused] generates MetaSequence let-bindings, meaning that it has to
   * occur before [simplify2]. Note that [in_memory] generates inner
   * let-bindings, so it has to be before [simplify2]. *)
  let files = if not !Options.struct_passing then Structs.pass_by_ref files else files in
  let files =
    if !Options.wasm then
      let files = Simplify.simplify2 files in
      let files = Structs.in_memory files in
      let files = Simplify.simplify2 files in
      (* This one near the end because [in_memory] generates new EBufCreate's that
       * need to be desugared. *)
      let files = SimplifyWasm.simplify files in
      files
    else
      files
  in
  let files = Structs.collect_initializers files in
  let files = Simplify.remove_unused files in
  let files = Simplify.simplify2 files in
  let files = Inlining.cross_call_analysis files in
  if !arg_print_structs then
    print PrintAst.print_files files;
  let has_errors, files = Checker.check_everything files in
  tick_print (not has_errors) "Structs + Simplify 2";

  (* 6. Anonymous unions break typing. *)
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

  if !Options.wasm && not (Options.debug "force-c") then
    (* Runtime support files first. *)
    let is_support, rest = List.partition (fun (name, _) -> name = "WasmSupport") files in
    if List.length is_support = 0 then
      Warnings.fatal_error "The module WasmSupport wasn't passed to kremlin!";
    let files = is_support @ rest in

    (* The Wasm backend diverges here. We go to [CFlat] (an expression
     * language), then directly into the Wasm AST. *)
    let files = AstToCFlat.mk_files files in
    tick_print true "AstToCFlat";

    let modules = CFlatToWasm.mk_files files in
    tick_print true "CFlatToWasm";

    OutputJs.write_all !js_files modules !arg_print_wasm

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

    Printf.printf "KreMLin: wrote out .c files for %s\n" (String.concat ", " (List.map fst files));
    Printf.printf "KreMLin: wrote out .h files for %s\n" (String.concat ", " (List.map fst headers));

    if !arg_skip_compilation then
      exit 0;
    let remaining_c_files = Driver.compile (List.map fst files) !c_files in

    if !arg_skip_linking then
      exit 0;
    Driver.link remaining_c_files !o_files
