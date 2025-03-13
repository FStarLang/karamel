(* Copyright (c) INRIA and Microsoft Corporation. All rights reserved. *)
(* Licensed under the Apache 2.0 and MIT Licenses. *)

(** KaRaMeL, a tool to translate from a minimal ML-like language to C. *)

module Time = struct
  let t = ref None

  let start () =
    t := Some (Unix.times ())

  let tick buf () =
    let t' = Unix.times () in
    let diff = t'.Unix.tms_cutime -. (Option.get !t).Unix.tms_cutime +.
      t'.Unix.tms_utime -. (Option.get !t).Unix.tms_utime
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

open Krml

let _ =
  let arg_version = ref false in
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
  let arg_skip_makefiles = ref false in
  let arg_diagnostics = ref false in
  let arg_verify = ref false in
  let arg_warn_error = ref "" in
  let arg_c89 = ref false in
  let c_files = ref [] in
  let o_files = ref [] in
  let js_files = ref [] in
  let fst_files = ref [] in
  let filenames = ref [] in
  let usage = Printf.sprintf
{|KaRaMeL: from a ML-like subset to C

Usage: %s [OPTIONS] FILES

High-level description:
  1. If some FILES end with .fst or .fsti, and [-verify] is set, KaRaMeL will
     call [fstar] on them to perform verification.
  2. If some FILES end with .fst or .fsti, KaRaMeL will call [fstar] on them to
     perform extraction and produce [out.krml].
  3. If exactly one FILE ends with [.krml] or [.json], or if a [.krml] file was
     produced at step 2., KaRaMeL will generate a series of [.c] and [.h] files
     in the directory specified by [-tmpdir], or in the current directory.
  4. If some FILES end with [.c], KaRaMeL will compile them along with the [.c]
     files generated at step 3. to obtain a series of [.o] files.
  5. If some FILES end with [.o], [.S] or [.a], KaRaMeL will link them along with the
     [.o] files obtained at step 4. to obtain a final executable.

The [-skip-extraction] option stops KaRaMeL after step 1.
The [-skip-translation] option stops KaRaMeL after step 2.
The [-skip-compilation] option stops KaRaMeL after step 3.
The [-skip-linking] option stops KaRaMeL after step 4.

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
  13: monomorphic instance about to be dropped
  14: cannot perform tail-call optimization
  15: function is not Low*; need compatibility headers
  16: arity mismatch -- typically code that is high-order in F* but not in C
  17: declaration generates a static initializer
  18: bundle collision
  19: assume val marked as ifdef cannot be translated to an ifdef (e.g. it
      appears in the wrong position)
  20: right-hand side of short-circuiting boolean operator gives rise to
      let-bindings, rewriting to an if-then-else
  21: cannot translate to macro
  22: dropping declaration at ctypes bindings generation time

The [-bundle] option takes an argument of the form Api=Pattern1,...,Patternn
The Api= part is optional and Api is made up of a non-empty list of modules
separated by + (for instance: Interface1+Interface2). A pattern is either Foo.Bar
(exact match) or Foo.Baz.* (prefix). The semantics are as follows: all the
modules that match a pattern are grouped into a single C translation unit, and
their declarations are marked as static, inasmuch as cross-translation unit
calls permit. If the Api= part is present, then the module named Api must be
found within the set of input files, and its declarations are appended to the
translation unit without any visibility modifications.

The default arguments are: %s

All include directories and paths supports special prefixes:
  - if a path starts with FSTAR_LIB, this will expand to wherever F*'s ulib
    directory is

Karamel will also enable some default options according to the the flavor of C
compiler being used.
%s
If the compiler flavor cannot be detected (and you ignore this error) no flags
will be added. You can force a flavor with the -ccflavor option.

The [-fc89] option triggers [-fnoanonymous-unions], [-fnocompound-literals] and
[-fc89-scope]. It also changes the invocations above to use [-std=c89]. Note
that if you're using the uint128 type, you will have to manually compile this
code with -DKRML_VERIFIED_UINT128.

To debug Wasm codegen, it might be useful to trigger the same compilation path
as Wasm, but emit C code instead. This can be achieved with [-wasm -d
force-c,c-calls,wasm-calls -drop C,TestLib -add-include '"hack.h"']
where [hack.h] contains [#define WasmSupport_check_buffer_size(X)].

Supported options:|}
    Sys.argv.(0)
    !Options.warn_error
    (String.concat " " (List.concat_map (fun b ->
      [ "-bundle"; Bundle.string_of_bundle b ]
    ) !Options.bundle @ List.concat_map (fun p ->
      [ "-drop"; Bundle.string_of_pattern p ]
    ) !Options.drop))
    (
      let open Options in
      let flavors = [GCC; Clang; Compcert; MSVC] in
      let p k = String.concat " " (Array.to_list (Options.default_options k)) in
      String.concat "\n" (
      List.map (fun k -> KPrint.bsprintf "  For %s adds [%s]" (Options.string_of_compiler_flavor k) (p k)) flavors)
    )
  in
  let found_file = ref false in
  let used_drop = ref false in
  let prepend r = fun s -> r := s :: !r in
  let parse_include s =
    let open Options in
    match String.split_on_char ':' s with
    | [ h; i ] ->
        begin match Filename.chop_suffix_opt ~suffix:".c" h with
        | Some h ->
            COnly h, i
        | None ->
            begin match Filename.chop_suffix_opt ~suffix:".h" h with
            | Some h ->
                InternalOnly h, i
            | None ->
                HeaderOnly h, i
            end
        end
    | [ i ] -> All, i
    | _ -> failwith ("Invalid -add-[early-|]include argument: " ^ s)
  in
  let csv f s =
    List.iter f (KString.split_on_char ',' s)
  in
  let spec = [
    (* KaRaMeL as a driver *)
    "-fstar", Arg.Set_string Options.fstar, " fstar.exe to use; defaults to \
      'fstar.exe'";
    "-cc", Arg.Set_string Options.cc, " compiler to use; default is 'cc', \
      you can also set the CC environment variable";
    "-ccflavor", Arg.String (fun s ->
        let flav = Options.compiler_flavor_of_string s in
        Options.cc_flavor := Some flav), " C compiler flavor; normally autodetected, \
        can be set to 'gcc', 'clang', 'compcert', 'msvc' or 'generic'";
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
    "-skip-makefiles", Arg.Set arg_skip_makefiles, " do not produce Makefile.basic, Makefile.include";
    "-verify", Arg.Set arg_verify, " ask F* to verify the program";
    "-verbose", Arg.Set Options.verbose, "  show the output of intermediary \
      tools when acting as a driver for F* or the C compiler";
    "-silent", Arg.Set Options.silent, "  hide timing, tool detection and \
      external commands messages";
    "-diagnostics", Arg.Set arg_diagnostics, "  list recursive functions and \
      overly nested data types (useful for MSVC)";
    "-wasm", Arg.Unit (fun () ->
      KPrint.beprintf "Warning: -wasm is deprecated, use -backend wasm instead\n";
      Options.(backend := Wasm)
    ), "  emit a .wasm file instead of C";
    "-backend", Arg.String (fun s ->
      let open Options in
      match String.lowercase_ascii s with
      | "wasm" -> backend := Wasm
      | "c" -> backend := C
      | "rust" -> backend := Rust; allow_tapps := true; PrintCommon.indent := 4
      | _ -> failwith ("unrecognized backend: " ^ s)
    ), "  generate code for either one of c (default), rust or wasm";
    "", Arg.Unit (fun _ -> ()), " ";

    (* Controlling the behavior of KaRaMeL *)
    "-add-early-include", Arg.String (fun s ->
      prepend Options.add_early_include (parse_include s)),
      "  prepend #include the-argument to every generated file, before krmllib.h";
    "-add-include", Arg.String (fun s ->
      prepend Options.add_include (parse_include s)), " prepend #include \
      the-argument to every generated file, after the #define __FOO_H";
    "-add-include-tmh", Arg.Set Options.add_include_tmh, "  append #include \
      <FILE.tmh>, where FILE is the current basename";
    "-minimal", Arg.Set Options.minimal, "  do not prepend #include \"krmllib.h\"; do \
      not bundle FStar";
    "-static-header", Arg.String (fun s ->
      List.iter (prepend Options.static_header) (Parsers.drop s)), " generate a \
      .h for the given module where all functions are marked a static inline";
    "-no-prefix", Arg.String (fun s -> List.iter (prepend Options.no_prefix) (Parsers.drop s)),
      " don't prepend the module name to declarations from module matching this \
      pattern";
    "-bundle", Arg.String (fun s -> prepend Options.bundle (Parsers.bundle s)), " \
      group F* modules into a single C translation unit or Rust file (see above)";
    "-crate", Arg.String (fun s -> prepend Options.crates (Parsers.bundle s)), " \
      adopt a Cargo workspace and group Rust files into a single sub-crate of \
      that workspace (see above) -- no empty left-hand side allowed, and note \
      that the right-hand side matches Rust file names (which may be the product \
      of bundling), NOT F* module sources";
    "-drop", Arg.String (fun s ->
      used_drop := true;
      List.iter (prepend Options.drop) (Parsers.drop s)),
      "  do not extract code for this module (see above)";
    "-library", Arg.String (fun s ->
      List.iter (prepend Options.library) (Parsers.drop s)),
      "  this is a model and all functions should be made abstract";
    "-hand-written", Arg.String (fun s ->
      List.iter (prepend Options.hand_written) (Parsers.drop s)),
      "  in conjunction with static-header and library";
    "-extract-uints", Arg.Set Options.extract_uints, ""; (* no doc, intentional *)
    "-record-renamings", Arg.Set Options.record_renamings, " write a map from \
      old names to new names in KrmlRenamings.h, useful if you're a library and \
      don't want to impose clients to follow all of your usages of rename-prefix";
    "-header", Arg.Set_string Options.header, " prepend the contents of the given \
      file at the beginning of each .c and .h";
    "-tmpdir", Arg.Set_string Options.tmpdir, " temporary directory for .out, \
      .c, .h and .o files";
    "-ctypes", Arg.String (fun s ->
      List.iter (prepend Options.ctypes) (Parsers.drop s)),
      "  also generate Ctypes OCaml bindings for these modules";
    "-rst-snippets", Arg.Set Options.rst_snippets, " generate SNIPPET_START and \
      SNIPPET_END directives for RST documentation";
    "-I", Arg.String (prepend Options.includes), " add directory to search path \
      (F* and C compiler)";
    "-o", Arg.Set_string Options.exe_name, "  name of the resulting executable";
    "-warn-error", Arg.String (fun s -> arg_warn_error := !arg_warn_error ^ s), "  decide which errors are \
      fatal / warnings / silent (default: " ^ !Options.warn_error ^")";

    (* Fine-tuning code generation. *)
    "", Arg.Unit (fun _ -> ()), " ";
    "-by-ref", Arg.String (fun s -> prepend Options.by_ref (Parsers.lid s)), " \
      pass the given struct type by reference, always";
    "-fno-box", Arg.Set Options.no_box, "  don't generate Box (Rust only)";
    "-fcontained-type", Arg.String (fun s -> Options.contained := s :: !Options.contained), "  \
      type passed by reference with a different lifetime";
    "-fkeep-tuples", Arg.Set Options.keep_tuples, "  do not monomorphize tuples";
    "-fbuiltin-uint128", Arg.Set Options.builtin_uint128, "  target compiler \
      supports arithmetic operators for uint128 -- this is NON PORTABLE, \
      works only with GCC/Clang";
    "-falloca", Arg.Set Options.alloca_if_vla, "  use alloca(3) for \
      variable-length arrays on the stack";
    "-fnostruct-passing", Arg.Clear Options.struct_passing, "  disable passing \
      structures by value and use pointers instead";
    "-fnoanonymous-unions", Arg.Clear Options.anonymous_unions, "  disable C11 \
      anonymous unions";
    "-fnocompound-literals", Arg.Clear Options.compound_literals,
      "  don't generate C11 compound literals";
    "-ftail-calls", Arg.Set Options.tail_calls, "  statically compile tail-calls \
      into loops";
    "-funroll-loops", Arg.Set_int Options.unroll_loops, "  loops whose number of \
      iterations is statically known to be smaller than the given argument and \
      smaller than 16 are compiled as macro calls KRML_MAYBE_FORN (N=2, 3, ..., 16); \
      then, at C compile-time, any KRML_MAYBE_FORN for N <= KRML_UNROLL_MAX gets \
      macro-expanded into a series of C blocks. KRML_UNROLL_MAX is initially \
      defined to be 16, but can be overridden at build-time for any given file \
      by passing -DKRML_UNROLL_MAX=N' to the compiler invocation. With this \
      option, loops with 0 iteration get eliminated and loops with 1 iteration \
      get replaced by the body.";
    "-fparentheses", Arg.Set Options.parentheses, "  add unnecessary parentheses \
      to silence GCC and Clang's -Wparentheses";
    "-fno-shadow", Arg.Set Options.no_shadow, "  add unnecessary renamings to \
      defeat GCC and Clang's -Wshadow, as well as the various MSVC warnings";
    "-fcurly-braces", Arg.Set Options.curly_braces, "  always add curly braces \
      around blocks";
    "-fnoshort-enums", Arg.Clear Options.short_enums, "  use C11 enums instead \
      of C macros and uint8_t for enums";
    "-fnoreturn-else", Arg.Set Options.no_return_else, "  if the body of an \
      if-block always returns (terminal position), don't insert an else block";
    "-fmerge", Arg.String (function
      | "aggressive" -> Options.(merge_variables := Aggressive)
      | "prefix" -> Options.(merge_variables := Prefix)
      | _ -> failwith "Unknown value for option -fmerge (must be one of: aggressive, prefix)"),
      "  merge variables together rather than emit shadowing let-bindings; \
        prefix restricts merges to variables that share a common prefix; \
        aggressive always merges";
    "-fc89-scope", Arg.Set Options.c89_scope, "  use C89 scoping rules";
    "-fcast-allocations", Arg.Set Options.cast_allocations, "  cast allocations (for C89, or for C++)";
    "-fc++-compat", Arg.Set Options.cxx_compat, "  make the \
      generated code compile both as C11 and C++20";
    "-fc++17-compat", Arg.Set Options.cxx17_compat, "  makes the code compile as C++17, but *NOT* as C \
      code";
    "-fc89", Arg.Set arg_c89, "  generate C89-compatible code (meta-option, see \
      above) + also disable variadic-length KRML_HOST_EPRINTF + cast allocations";
    "-flinux-ints", Arg.Set Options.linux_ints, " use Linux kernel int types";
    "-fmicrosoft", Arg.Set Options.microsoft, " various Microsoft-specific \
      tweaks";
    "-fextern-c", Arg.Set Options.extern_c, " wrap declarations in each header \
      with extern \"C\" {";
    "-fnoshort-names", Arg.Clear Options.short_names, "  disable unprefix names \
      for private (static) functions that are not exposed in headers; this ensures \
      robust collision-avoidance in case your private function names collide with \
      one of the included system headers";
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
      inline,bundle,reachability,c-calls,c-names,wasm-calls,wasm-memory,wasm,force-c,cflat";
    "", Arg.Unit (fun _ -> ()), " ";

      (* General utilities *)
    "-version", Arg.Set arg_version, " Display version number";
  ] in
  let spec = Arg.align spec in
  let rec anon_fun f =
    if String.length f > 0 && f.[0] = '@' && Filename.check_suffix f ".rsp" then
      let response_file = String.sub f 1 (String.length f - 1) in
      let lines = ref [ Sys.argv.(0) ] in
      Utils.with_open_in response_file (fun c ->
        try
          while true do
            let l = input_line c in
            if l.[String.length l - 1] = '\r' then
              lines := String.sub l 0 (String.length l - 1) :: !lines
            else
              lines := l :: !lines
          done
        with End_of_file ->
          ()
      );
      Arg.parse_argv ~current:(ref 0) (Array.of_list (List.rev !lines)) spec anon_fun usage
    else begin
      if Filename.check_suffix f ".fst" || Filename.check_suffix f ".fsti" then
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
        Warn.fatal_error "Unknown file extension for %s\n" f;
      found_file := true
    end
  in
  begin try
    Arg.parse spec anon_fun usage
  with Sedlexing.MalFormed | Sedlexing.InvalidCodepoint _ | KParser.Error ->
    KPrint.bprintf "Complete invocation was: %s\n"
      (String.concat "␣" (Array.to_list Sys.argv));
    exit 1
  end;

  if !arg_version then begin
    Printf.printf "KaRaMeL version: %s\n" Version.version;
    exit 0
  end;

  if not !found_file ||
     List.length !fst_files = 0 && List.length !filenames = 0 ||
     List.length !fst_files > 0 && List.length !filenames > 0
  then begin
    print_endline (Arg.usage_string spec usage);
    exit 1
  end;

  if !Options.unroll_loops > 16 && not (Options.rust ()) then begin
    print_endline "Error: argument to -funroll-loops cannot be greater than 16";
    exit 1
  end;

  let user_ccopts = !Options.ccopts in

  (* First enable the default warn-error string. *)
  Warn.parse_warn_error !Options.warn_error;

  (* Non-negotiable: the whole world has to be in agreement about what is
   * already in the krmllib header, otherwise there will be two definitions in
   * scope, one with internal linkage and possibly one with external linkage if
   * some client of krmllib runs without this option. Let's avoid that. Note
   * that there is also a per-definition criterion in CStarToC11.ml to
   * selectively mark some of the definitions in machine integers as static
   * inline. *)
  Options.static_header := [
    Bundle.Module [ "C"; "Endianness" ];
    Bundle.Module [ "LowStar"; "Endianness" ];
    Bundle.Module [ "FStar"; "UInt128" ]
  ] @ !Options.static_header;

  (* Meta-options that enable other options. Do this now because it influences
   * the default options for each compiler. *)
  if Options.wasm () then begin
    Options.anonymous_unions := false;
    Options.struct_passing := false;

    (* True Wasm compilation: this module is useless (only assume val's). *)
    (* Only keep what's stricly needed from the C module. *)
    Options.bundle := ([], [ Bundle.Module [ "C"; "Compat" ]], []) :: ([], [ Bundle.Module [ "C" ]], []) :: !Options.bundle;
    Options.extract_uints := true;

    (* Self-help. *)
    if Options.debug "force-c" then begin
      Options.(add_include := (All, "\"krml/internal/wasmsupport.h\"") :: !add_include);
      Options.drop := Bundle.Module [ "WasmSupport" ] :: !Options.drop
    end
  end;

  if not !Options.minimal then
    Options.bundle :=
      ([], [ Bundle.Module [ "C"; "Loops" ];
        Bundle.Module [ "C"; "Compat"; "Loops" ];
        Bundle.Module [ "Spec"; "Loops" ] ], []) ::
      ([], [ Bundle.Module [ "Prims" ] ], []) ::
      ([], [ Bundle.Prefix [ "FStar" ] ], []) ::
      ([], [ Bundle.Prefix [ "LowStar" ] ], []) ::
      ([], [ Bundle.Prefix [ "WasmSupport" ] ], []) ::
      !Options.bundle;

  if !arg_c89 then begin
    Options.anonymous_unions := false;
    Options.compound_literals := false;
    Options.cast_allocations := true;
    Options.c89_scope := true;
    Options.c89_std := true;
    Options.ccopts := Driver.Dash.d "KRML_VERIFIED_UINT128" :: !Options.ccopts
  end;

  (* Then refine that based on the user's preferences. *)
  if !arg_warn_error <> "" then
    Warn.parse_warn_error !arg_warn_error;

  if !used_drop then
    Warn.(maybe_fatal_error ("", Error.Deprecated ("-drop", "use a combination of \
      -bundle and -d reachability to make sure the functions are eliminated as \
      you wish")));

  (* Timings. *)
  Time.start ();
  let tick_print ok fmt =
    if not !Options.silent then begin
      flush stdout;
      flush stderr;
      if ok then
        Printf.printf ("%s✔%s [" ^^ fmt) Ansi.green Ansi.reset
      else
        Printf.printf ("%s⚠%s [" ^^ fmt) Ansi.red Ansi.reset;
      KPrint.bprintf "] %a\n" Time.tick ()
    end
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

  (* Empty file generated by F*, we provide the missing bits in src/Builtin.ml *)
  let filenames = List.filter (fun f -> Filename.basename f <> "prims.krml") filenames in
  let files = InputAst.read_files filenames in

  (* -djson *)
  if !arg_print_json then
    Yojson.Safe.to_channel stdout (InputAst.binary_format_to_yojson (InputAst.current_version, files));

  (* -dast *)
  let files = Builtin.prepare (InputAstToAst.mk_files files) in
  if !arg_print_ast then
    print PrintAst.print_files files;

  (* 0. Since the user may now pass several .krml files in an arbitrary order,
   * we need a topological order. Example:
   * - B.g depends on A.f and they both bundled (and private)
   * - A needs to come before B so that in the resulting bundle, "static void
   *   A_f" comes before "static void B_g" (since they're static, there's no
   *   forward declaration in the header. *)
  let files = Builtin.make_libraries files in
  let files = if Options.wasm () then SimplifyWasm.intrinsics#visit_files () files else files in
  let files = Bundles.topological_sort files in
  if Options.debug "topological" then
    KPrint.bprintf "file order after first topological sort: %s\n"
      (String.concat " " (List.map fst files));

  (* 1. We create bundles, and monomorphize functions first. This creates more
   * applications of parameterized types, which we make sure are in the AST by
   * checking it. Note that bundling calls [drop_unused] already to do a first
   * round of unused code elimination! *)
  let files = Bundles.make_bundles files in
  let has_spinlock = List.exists (fun (_, ds) ->
    List.exists (fun d ->
      fst (Ast.lid_of_decl d) = [ "Steel"; "SpinLock" ]
    ) ds
  ) files in
  (* This needs to happen before type monomorphization, so that list<t> and
   * list<t'> don't generate two distinct declarations (e.g. list__t and
   * list__t'). Also needs to happen before monomorphization of equalities. *)
  let files = Inlining.inline_type_abbrevs files in
  let files = DataTypes.remove_unused_type_arguments files in
  let files = Inlining.reparenthesize_applications files in
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
   * spurious dependencies otherwise. Requires accurate use count. *)
  let files = DataTypes.simplify files in
  let files = Monomorphization.datatypes files in
  let files = DataTypes.optimize files in
  let files = Monomorphization.equalities files in
  let files = Inlining.inline files in
  let files = Inlining.drop_unused files in
  if !arg_print_inline then
    print PrintAst.print_files files;
  let has_errors, files = Checker.check_everything files in
  tick_print (not has_errors) "Inlining";

  (* 3. Compile data types and pattern matches to enums, structs, switches and
   * if-then-elses. Better have monomorphized functions first! *)

  (* This needs to come after monomorphization of equalities -- otherwise the
     insertion of pointers will make things look like pointer equalities for
     which the recursive equality predicates are not generated. *)
  let files = GcTypes.heap_allocate_gc_types files in
  (* Note: this phase re-inserts some type abbreviations. *)
  let datatypes_state, files = DataTypes.everything files in
  (* Avoid polluting our scope with:
      abbrev k___chosen_internal_name = foo
    stemming from the monomorphization then elimination of type bar x = | Foo of foo
  *)
  let files = Inlining.inline_type_abbrevs ~just_auto_generated:true files in
  if !arg_print_pattern then
    print PrintAst.print_files files;
  let has_errors, files = Checker.check_everything files in
  tick_print (not has_errors) "Pattern matches compilation";

  (* 4. Whole-program transformations related to structs.
   *
   * - In C11, structures are values; they can be passed by value in function
   *   calls; compound literals allow creating them at any position within
   *   expressions
   * - In C89, compound literals are not available, meaning we need to go
   *   through an (uninitialized) allocation followed by an in-place
   *   initialization (structures that contain no union fields could use an
   *   initializer list but it's not super readable so we don't do that)
   * - In Wasm, structures are not values, meaning that all structures need to
   *   have an address and be passed by address; compound literals are not
   *   available, meaning that we need to allocate + write initial value. This
   *   enforces correct evaluation semantics.
   *
   * In the code below...
   * - For C11, we do nothing in particular.
   * - For C89, we "explode" compound literals as allocations + assignments.
   * - For Wasm, we rewrite function calls to not pass structures as values.
   *     Note: we offer this as a standalone option, which complicates the logic.
   *     If the rewriting were to be performed only for Wasm, then the "pass by
   *     ref" transformation could occur after the "in memory" transformation and
   *     would be MUCH simplier.
   *   Then, we rewrite the code to allocate every struct expression as a stack
   *   allocation in scope, followed by writing the initial value. This is done
   *   in two steps: first, "in memory" generates EBufCreate nodes and
   *   guarantees that EFlat (structures) only appears as arguments to
   *   EBufCreate. Then, "simplify wasm 2" rewrites this in EBufCreate EAny
   *   followed by EBufWrite, per the precondition of AstToCFlat.
   *
   * There is an extraneous call to "simplify 2" before "in memory"; it would be
   * good to remove it. *)
  let files = if not !Options.struct_passing || has_spinlock then Structs.pass_by_ref files else files in
  let files =
    if Options.wasm () then
      let files = Simplify.sequence_to_let#visit_files () files in
      let files = Simplify.optimize_lets files in
      let files = SimplifyWasm.simplify1 files in
      let files = Simplify.hoist#visit_files [] files in
      let files = Structs.in_memory files in
      (* This one near the end because [in_memory] generates new EBufCreate's that
       * need to be desugared into EBufCreate Any + EBufWrite. See e2ceb92e. *)
      let files = SimplifyWasm.simplify2 files in
      let files = Simplify.let_to_sequence#visit_files () files in
      tick_print true "Wasm specific";
      files
    else if not !Options.compound_literals then
      Structs.remove_literals files
    else
      files
  in
  let files = if not (Options.wasm ()) then Simplify.simplify1 files else files in
  let files = if not (Options.wasm ()) then Structs.collect_initializers files else files in
  (* Need correct private qualifiers for remove_unused to drop arguments for
   * static declarations. *)
  let files = Inlining.cross_call_analysis files in
  (* Note: generates let-bindings, so needs to be before simplify2 *)
  let files = Simplify.remove_unused files in
  let files = if !Options.tail_calls then Simplify.tail_calls files else files in

  (* This allows drop'ing the module that contains just ifdefs. *)
  let ifdefs = AstToCStar.mk_ifdefs_set files in
  let macros = AstToCStar.mk_macros_set files in

  let files = if Options.rust () then SimplifyRust.simplify_ast files else files in
  let files = Simplify.simplify2 ifdefs files in
  let files = Inlining.mark_possibly_unused ifdefs files in
  let files = if Options.(!merge_variables <> No) then SimplifyMerge.simplify files else files in
  if !arg_print_structs then
    print PrintAst.print_files files;
  Structs.check_for_illegal_copies files;
  let has_errors, files = Checker.check_everything files in
  tick_print (not has_errors) "Structs + Simplify 2";

  (* 5. Anonymous unions break typing. *)
  let files =
    if !Options.anonymous_unions && not (Options.rust ()) then
      DataTypes.anonymous_unions datatypes_state files
    else
      files
  in

  (* 6. Drop both files and selected declarations within some files, as a [-drop
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

  Diagnostics.all files !arg_diagnostics;

  (* 7. Final transformation on the AST: go to C names. This must really be done
   * at the last minute, since it invalidates pretty much any map ever built.
   * For instance, we compute dependencies now rather than have to deal with
   * potential name conflicts owing to global collisions after dropping the
   * prefix for static declarations. *)
  let c_name_map = Simplify.allocate_c_names files in

  if Options.wasm () && not (Options.debug "force-c") then
    (* Runtime support files first. *)
    let is_support, rest = List.partition (fun (name, _) -> name = "WasmSupport") files in
    if List.length is_support = 0 then
      Warn.fatal_error "The module WasmSupport wasn't passed to karamel or \
        was hidden in a bundle!";

    let files = is_support @ rest in
    (* The Wasm backend diverges here. We go to [CFlat] (an expression
     * language), then directly into the Wasm AST. *)
    let layouts, files = AstToCFlat.mk_files files c_name_map in
    let files = List.filter (fun (_, decls) -> List.length decls > 0) files in
    tick_print true "AstToCFlat";

    let modules = CFlatToWasm.mk_files files in
    tick_print true "CFlatToWasm";

    let modules = OptimizeWasm.optimize_files modules in
    tick_print true "OptimizeWasm";

    OutputJs.write_all !js_files modules !arg_print_wasm layouts

  else if Options.rust () then
    let files = Simplify.sequence_to_let#visit_files () files in
    if Options.debug "rs" then
      print PrintAst.print_files files;
    let files = AstToMiniRust.translate_files files in
    let files = OptimizeMiniRust.cleanup_minirust files in
    let files = OptimizeMiniRust.infer_mut_borrows files in
    let files = OptimizeMiniRust.simplify_minirust files in
    OutputRust.write_all files

  else
    let () = () in
    Driver.maybe_create_output_dir ();
    if KString.starts_with !Options.exe_name "lib" then
      Output.write_def c_name_map files;


    (* Translate to C*... *)
    let file_of_map = Bundle.mk_file_of files in
    let deps = Bundles.direct_dependencies_with_internal files file_of_map in
    let files = AstToCStar.mk_files files c_name_map ifdefs macros in
    tick_print true "AstToCStar";

    let files = List.filter (fun (_, decls) -> List.length decls > 0) files in

    (* ... then to C *)
    let headers = CStarToC11.mk_headers c_name_map files in
    let deps = CStarToC11.drop_empty_headers deps headers in
    let internal_headers = Bundles.StringSet.of_list
      (List.filter_map (function (name, C11.Internal _) -> Some name | _ -> None) headers)
    in
    let public_headers = Bundles.StringSet.of_list
      (List.filter_map (function (name, C11.Public _) -> Some name | _ -> None) headers)
    in
    (* Bundles.debug_deps deps; *)
    let ml_files  = GenCtypes.mk_ocaml_bindings files c_name_map file_of_map in
    let files = CStarToC11.mk_files c_name_map files in
    let files = List.filter (fun (_, decls) -> List.length decls > 0) files in
    tick_print true "CStarToC";

    (* -dc *)
    if !arg_print_c then
      print PrintC.print_files files;

    flush stdout;
    flush stderr;
    Output.maybe_create_internal_dir headers;
    let c_output = Output.write_c files internal_headers deps in
    let h_output = Output.write_h headers public_headers deps in
    GenCtypes.write_bindings ml_files;
    GenCtypes.write_gen_module ~public:public_headers ~internal:internal_headers ml_files;
    if not !arg_skip_makefiles then
      Output.write_makefile user_ccopts !c_files c_output h_output;
    if !Options.record_renamings then
      Output.write_renamings c_name_map;

    tick_print true "PrettyPrinting";

    if not !Options.silent then begin
      Printf.printf "KaRaMeL: wrote out .c files for %s\n" (String.concat ", " (List.map fst files));
      Printf.printf "KaRaMeL: wrote out .h files for %s\n" (String.concat ", "
        (List.map (function | h, C11.Internal _ -> "internal/"^h | h, C11.Public _ -> h) headers))
    end;

    let ml_files = GenCtypes.file_list ml_files in
    if not (KList.is_empty !Options.ctypes) then
      Printf.printf "KaRaMeL: wrote out .ml files for %s\n" (String.concat ", " ml_files);

    if !arg_skip_compilation then
      exit 0;

    let cc_flavor_callback (k : Options.compiler_flavor) : unit =
      (* With the compiler flavor detected, add the default options for the compiler.
         We just call the option parser again to process the default_options. *)
      let ccopts = !Options.ccopts in
      Options.ccopts := [];
      Arg.parse_argv ~current:(ref 0)
        (Array.append [| Sys.argv.(0) |] (Options.default_options k))
        spec anon_fun usage;
      Options.ccopts := ccopts @ !Options.ccopts;
    in

    Driver.cc_flavor_callback := cc_flavor_callback;

    let remaining_c_files = Driver.compile (List.map fst files) !c_files in

    if !arg_skip_linking then
      exit 0;
    Driver.link remaining_c_files !o_files
