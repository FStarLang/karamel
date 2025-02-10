(* Copyright (c) INRIA and Microsoft Corporation. All rights reserved. *)
(* Licensed under the Apache 2.0 and MIT Licenses. *)

(** A very boring module that detects the environment and figures out how to
 * call the tools. *)

open Warn

(** These three filled in by [detect_cc] and others *)
let cc = ref ""
let cc_args = ref []
let cc_flavor = ref Options.Generic

(* Abstracting over - (dash) for msvc. vs. gcc-like. This module
 reads cc_flavor. *)
module Dash = struct
  let i dir =
    if !cc_flavor = MSVC then
      [ "/I"; dir ]
    else
      [ "-I"; dir ]

  let c file =
    if !cc_flavor = MSVC then
      [ "/c"; file ]
    else
      [ "-c"; file ]

  let d opt =
    if !cc_flavor = MSVC then
      "/D" ^ opt
    else
      "-D" ^ opt

  let o_obj file =
    if !cc_flavor = MSVC then
      [ "/Fo:"; file ]
    else
      [ "-o"; file ]

  let o_exe file =
    if !cc_flavor = MSVC then
      [ "/Fe:"; file ]
    else
      [ "-o"; file ]
end


module P = Process
(* Note: don't open [Process], otherwise any reference to [Output] will be
 * understood as a cyclic dependency on our own [Output] module. *)

let cc_flavor_callback = ref (fun (_ : Options.compiler_flavor) -> ())

(** These three variables filled in by [detect_fstar] *)
let fstar = Options.fstar
let fstar_lib = ref ""
let fstar_rev = ref "<unknown>"
let fstar_options = ref []

(** By [detect_karamel] *)
let krmllib_dir = ref ""
let runtime_dir = ref ""
let include_dir = ref ""
let misc_dir = ref ""
let krml_rev = ref "<unknown>"

(** The base tools *)
let readlink = ref ""

(* All our paths use "/" as a separator, INCLUDING windows paths because
 * they're run through cygpath -m *)
let (^^) x y = x ^ "/" ^ y

let d = Filename.dirname

let mkdirp d =
  let rec mkdirp d =
    if Sys.file_exists d then begin
      if not (Sys.is_directory d) then
        failwith "mkdirp: trying to recursively create a directory, but the file \
          exists already and is not a directory: %s" d
    end else begin
      mkdirp (Filename.dirname d);
      try Unix.mkdir d 0o755
      with
      | Unix.Unix_error (Unix.EEXIST, _, _) when Sys.is_directory d -> () (* raced with another process *)
      | _ as e -> raise e
    end
  in
  (* On Windows, the Filename function defines only \\ to be the path separator,
   * but in a Cygwin spirit, we want to accept either. This is an approximation. *)
  let d = if Sys.os_type = "Win32" then String.map (function '/' -> '\\' | x -> x) d else d in
  (* Note: on windows, Sys.file_exists "a\\b" == true (if b is a directory)
   * but Sys.file_exists "a\\b\\" == false -- this differs from other OSes *)
  let d = if d.[String.length d - 1] = '\\' then String.sub d 0 (String.length d - 1) else d in
  mkdirp d

let maybe_create_output_dir () =
  if !Options.tmpdir <> "" then
    mkdirp !Options.tmpdir

(** Check whether a command exited successfully *)
let success cmd args =
  try
    match Process.run cmd args with
    | { Process.Output.exit_status = Process.Exit.Exit 0; _ } -> true
    | _ -> false
  with Unix.Unix_error (Unix.ENOENT, _, _) ->
    (* command not found *)
    false

let read_one_line cmd args =
  String.trim (List.hd (Process.read_stdout cmd args))

let read_one_error_line cmd args =
  match Process.run cmd args with
  | { Process.Output.stderr; _ } ->
      String.trim (List.hd stderr)

(** The tools we depend on; namely, readlink. *)
let detect_base_tools () =
  if not !Options.silent then
    KPrint.bprintf "%s⚙ KaRaMeL auto-detecting tools.%s Here's what we found:\n" Ansi.blue Ansi.reset;

  if success "which" [| "greadlink" |] then
    readlink := "greadlink"
  else
    readlink := "readlink";
  begin try
    if read_one_line "uname" [||] = "Darwin" && !readlink = "readlink" then
      KPrint.bprintf "Warning: OSX detected and no greadlink found. Suggestion: \
        [brew install coreutils]\n";
  with
  | Process.Exit.Error _           (* command returned non-zero code *)
  | Unix.Unix_error (Unix.ENOENT, _, _) (* command not found *)
    -> ()
  end;
  if not !Options.silent then
    KPrint.bprintf "%sreadlink is:%s %s\n" Ansi.underline Ansi.reset !readlink

let detect_base_tools_if () =
  if !readlink = "" then
    detect_base_tools ()


(** Fills in *_dir, and fills in [Options.includes]. *)
let detect_karamel () =
  detect_base_tools_if ();

  if AutoConfig.krmllib_dir <> "" && try ignore (Sys.getenv "KRML_HOME"); false with Not_found -> true then begin
    krmllib_dir := AutoConfig.krmllib_dir;
    runtime_dir := AutoConfig.runtime_dir;
    include_dir := AutoConfig.include_dir;
    misc_dir := AutoConfig.misc_dir
  end else begin

    if not !Options.silent then
      KPrint.bprintf "%sKaRaMeL called via:%s %s\n" Ansi.underline Ansi.reset Sys.argv.(0);

    let krml_home =
      begin try
        Sys.getenv "KRML_HOME"
      with Not_found -> try
        let real_krml =
          let me = Sys.argv.(0) in
          if Sys.os_type = "Win32" && not (Filename.is_relative me) then
            me
          else
            try read_one_line !readlink [| "-f"; read_one_line "which" [| me |] |]
            with _ -> fatal_error "Could not compute full krml path"
        in
        (* src/_build/default/Karamel.exe *)
        if not !Options.silent then
          KPrint.bprintf "%sthe Karamel executable is:%s %s\n" Ansi.underline Ansi.reset real_krml;
        read_one_line !readlink [| "-f"; d real_krml ^^ ".." ^^ ".." ^^ ".." |]
      with _ ->
        fatal_error "Could not compute krml_home"
      end
    in
    if not !Options.silent then
      KPrint.bprintf "%sKaRaMeL home is:%s %s\n" Ansi.underline Ansi.reset krml_home;

    if try Sys.is_directory (krml_home ^^ ".git") with Sys_error _ -> false then begin
      let cwd = Sys.getcwd () in
      Sys.chdir krml_home;
      krml_rev := String.sub (read_one_line "git" [| "rev-parse"; "HEAD" |]) 0 8;
      Sys.chdir cwd
    end;

    krmllib_dir := krml_home ^^ "krmllib";
    runtime_dir := krml_home ^^ "runtime";
    include_dir := krml_home ^^ "include";
    misc_dir := krml_home ^^ "misc"

  end;

  (* The first one for the C compiler, the second one for F* *)
  Options.includes := !include_dir :: !Options.includes @ [ !krmllib_dir ]

let detect_karamel_if () =
  if !krmllib_dir = "" then
    detect_karamel ()

let expand_prefixes s =
  if KString.starts_with s "FSTAR_LIB" then
    !fstar_lib ^^ KString.chop s "FSTAR_LIB"
  else
    s

(* Fills in fstar{,_lib,_options}. Does NOT read any environment variables. *)
let detect_fstar () =
  detect_karamel_if ();

  if not !Options.silent then
    KPrint.bprintf "%s⚙ KaRaMeL will drive F*.%s Here's what we found:\n" Ansi.blue Ansi.reset;

  (* Try to resolve fstar to an absolute path. This is just so the
     full path appears in logs. *)
  if not (KString.starts_with !fstar "/") then begin
    try fstar := read_one_line "which" [| !fstar |]
    with _ -> ()
  end;

  if not !Options.silent then
    KPrint.bprintf "Using fstar.exe = %s\n" !fstar;

  (* Ask F* for the location of its library *)
  begin try fstar_lib := read_one_line !fstar [| "--locate_lib" |]
  with | _ ->
    fatal_error "Could not locate F* library: %s --locate_lib failed" !fstar
  end;
  if not !Options.silent then
    KPrint.bprintf "F* library root: %s\n" !fstar_lib;

  if success "which" [| "cygpath" |] then begin
    fstar := read_one_line "cygpath" [| "-m"; !fstar |];
    if not !Options.silent then
      KPrint.bprintf "%sfstar converted to windows path:%s %s\n" Ansi.underline Ansi.reset !fstar;
    fstar_lib := read_one_line "cygpath" [| "-m"; !fstar_lib |];
    if not !Options.silent then
      KPrint.bprintf "%sfstar lib converted to windows path:%s %s\n" Ansi.underline Ansi.reset !fstar_lib
  end;

  (* Record F* version, as output by the executable. *)
  begin try
    let lines = Process.read_stdout !fstar [| "--version" |] in
    fstar_rev := String.trim (String.concat " " lines);
    if not !Options.silent then
      KPrint.bprintf "%sfstar version:%s %s\n" Ansi.underline Ansi.reset !fstar_rev
  with | _ -> ()
  end;

  let fstar_includes = List.map expand_prefixes !Options.includes in
  fstar_options := [
    "--trace_error";
    "--expose_interfaces"
  ] @ List.flatten (List.rev_map (fun d -> ["--include"; d]) fstar_includes);
  (* This is a superset of the needed modules... some will be dropped very early
   * on in Karamel.ml *)

  (* Locate and pass FStar.UInt128 *)
  let fstar_locate_file f =
    try read_one_line !fstar [| "--locate_file"; f |]
    with
    | _ ->
      Warn.fatal_error "Could not locate file %s, is F* properly installed?" f
  in
  fstar_options := fstar_locate_file "FStar.UInt128.fst" :: !fstar_options;

  fstar_options := (!runtime_dir ^^ "WasmSupport.fst") :: !fstar_options;
  if not !Options.silent then
    KPrint.bprintf "%sfstar is:%s %s %s\n" Ansi.underline Ansi.reset !fstar (String.concat " " !fstar_options);

  flush stdout

let detect_fstar_if () =
  if !fstar = "" then
    detect_fstar ()

let expand_prefixes s =
  detect_fstar_if ();
  expand_prefixes s

let verbose_msg () =
  if !Options.verbose then
    ""
  else
    " (use -verbose to see the output)"

(** Run a command, print its output if [-verbose] is passed, and possibly abort
 * (depending on -warn-error) if the command failed. *)
let run_or_warn str exe args =
  let debug_str = KPrint.bsprintf "%s %s" exe (String.concat " " args) in
  if !Options.verbose then
    print_endline debug_str;
  let r = P.run exe (Array.of_list args) in
  flush stdout; flush stderr;
  match r with
  | { P.Output.exit_status = P.Exit.Exit 0; stdout; stderr; _ } ->
      if not !Options.silent then
        KPrint.bprintf "%s✔%s %s%s\n" Ansi.green Ansi.reset str (verbose_msg ());
      if !Options.verbose then
        List.iter print_endline stdout;
        List.iter print_endline stderr;
      true
  | { P.Output.stderr; stdout; _ } ->
      KPrint.bprintf "%s✘%s %s%s\n" Ansi.red Ansi.reset str (verbose_msg ());
      List.iter print_endline stderr;
      List.iter print_endline stdout;
      Stdlib.(flush stdout; flush stderr);
      maybe_fatal_error ("run_or_warn", ExternalError debug_str);
      false

(** Called from the top-level file; runs [fstar] on the [.fst] files
 * passed on the command-line, and returns the name of the generated file. *)
let run_fstar verify skip_extract skip_translate files =
  assert (List.length files > 0);
  detect_fstar_if ();

  if not !Options.silent then
    KPrint.bprintf "%s⚡ Calling F* (use -verbose to see the output)%s\n" Ansi.blue Ansi.reset;
  let args = List.rev !Options.fsopts @ !fstar_options @ List.rev files in
  if verify then begin
    flush stdout;
    if not (run_or_warn "[verify]" !fstar args) then
      fatal_error "F* failed"
  end;

  if skip_extract then
    exit 0
  else
    let args =
      "--odir" :: !Options.tmpdir ::
      "--codegen" :: "krml" ::
      "--lax" :: args
    in
    flush stdout;
    maybe_create_output_dir ();
    if not (run_or_warn "[F*,extract]" !fstar args) then
      fatal_error "F* failed";
    if skip_translate then
      exit 0;
    !Options.tmpdir ^^ "out.krml"

let detect_compiler_flavor cc =
  let is_gcc () =
    try
      (* If cc points to gcc, cc --version will say "cc version ...", instead of
      gcc. So use -v instead, but that prints to stderr. *)
      let rc = Process.run cc [| "-v" |] in
      let lines = rc.stderr in
      List.exists (fun l -> KString.starts_with l "gcc version") lines
    with | _ -> false
  in
  let is_clang () =
    try
      let lines = Process.read_stdout cc [| "--version" |] in
      List.exists (fun l -> KString.exists l "clang version") lines
    with | _ -> false
  in
  let is_compcert () =
    try
      let lines = Process.read_stdout cc [| "--version" |] in
      List.exists (fun l -> KString.exists l "CompCert") lines
    with | _ -> false
  in
  let is_msvc () =
    try
      let rc = Process.run cc [| |] in
      let lines = rc.stderr in
      List.exists (fun l -> KString.exists l "Microsoft") lines
    with | _ -> false
  in
  if is_gcc ()           then Options.GCC
  else if is_clang ()    then Options.Clang
  else if is_compcert () then Options.Compcert
  else if is_msvc ()     then Options.MSVC
  else (
    Warn.maybe_fatal_error ("detect_compiler_flavor", UnrecognizedCCompiler cc);
    Generic
  )

let fill_cc_args () =
  (** For the side-effect of filling in [Options.includes] *)
  detect_karamel_if ();

  cc_args :=
    (if not !Options.struct_passing then [ Dash.d "KRML_NOSTRUCT_PASSING" ] else [])
    @ Dash.i (!krmllib_dir ^^ "dist" ^^ "minimal")
    @ List.flatten (List.rev_map Dash.i (!Options.tmpdir :: !Options.includes))
    @ List.rev !Options.ccopts
    @ !cc_args

(* Sets cc, cc_flavor *)
let auto_detect_cc () =
  (* !cc can be relative or absolute, `which` handles both. *)
  if not (success "which" [| !cc |]) then
    Warn.fatal_error "C compiler '%s' not found!" !cc;

  if not !Options.silent then begin
    (* If not absolute print realpath too *)
    let real =
      if KString.starts_with !cc "/" then
        ""
      else
        match
          read_one_line !readlink [| "-f"; read_one_line "which" [| !cc |] |]
        with
        | exception _ -> " (couldn't resolve?)"
        | s -> " (= " ^ s ^ ")"
    in
    KPrint.bprintf "%scc is:%s %s%s\n" Ansi.underline Ansi.reset !cc real
  end;
  match !Options.cc_flavor with
  | Some f -> cc_flavor := f
  | None ->   cc_flavor := detect_compiler_flavor !cc

let detect_cc () =
  detect_base_tools_if ();

  if not !Options.silent then
    KPrint.bprintf "%s⚙ KaRaMeL will drive the C compiler.%s Here's what we found:\n" Ansi.blue Ansi.reset;

  (* Use Options.cc if passed, otherwise CC from env, otherwise "cc" *)
  let cc_name =
    if !Options.cc <> ""
    then !Options.cc
    else
      match Sys.getenv "CC" with
      | s -> s
      | exception _ -> "cc"
  in

  if cc_name = "msvc" then (
    (* We special-case "msvc" and use this wrapper script to find it
       and set its environment up, it's not really feasible to
       just find the cl.exe *)
    KPrint.bprintf "%scc is:%s MSVC (will use cl-wrapper script)\n" Ansi.underline Ansi.reset;
    cc := !misc_dir ^^ "cl-wrapper.bat";
    cc_flavor := MSVC
  ) else (
    (* Otherwise cc_name is a normal command or path like gcc/clang,
       auto-detect its flavor. *)
    cc := cc_name;
    auto_detect_cc ()
  );

  if not !Options.silent then
    KPrint.bprintf "%scc flavor is:%s %s\n" Ansi.underline Ansi.reset
      (Options.string_of_compiler_flavor !cc_flavor);

  (* Now that we detected the flavor, call this callback to
     right default arguments for the compiler filled in. *)
  !cc_flavor_callback !cc_flavor;

  fill_cc_args ();

  if !cc_flavor = GCC && !Options.m32 then
    cc_args := "-m32" :: !cc_args;

  if not !Options.silent then
    KPrint.bprintf "%scc options are:%s %s\n" Ansi.underline Ansi.reset
      (String.concat " " !cc_args)

let detect_cc_if () =
  if !cc = "" then
    detect_cc ()

let o_of_c f =
  let dot_o = if !cc_flavor = MSVC then ".obj" else ".o" in
  !Options.tmpdir ^^ Filename.chop_suffix (Filename.basename f) ".c" ^ dot_o


(** For "krmllib.c", and every [.c] file generated by Karamel or passed on the
 * command-line, run [gcc -c] to obtain a [.o]. Files that don't compile are
 * silently dropped, or KaRaMeL aborts if warning 3 is fatal. *)
let compile files extra_c_files =
  assert (List.length files > 0);
  let extra_c_files = List.map expand_prefixes extra_c_files in
  detect_karamel_if ();
  detect_cc_if ();
  flush stdout;

  let files = List.map (fun f -> !Options.tmpdir ^^ f ^ ".c") files in
  if not !Options.silent then
    KPrint.bprintf "%s⚡ Generating object files%s\n" Ansi.blue Ansi.reset;
  let gcc_c file =
    flush stdout;
    let info = Printf.sprintf "[CC,%s]" file in
    let args = !cc_args @ Dash.c file @ Dash.o_obj (o_of_c file) in
    run_or_warn info !cc args
  in

  let files = List.filter gcc_c files in
  let extra_c_files = List.filter gcc_c extra_c_files in

  let ide_support = open_out (!Options.tmpdir ^^ "compile_flags.txt") in
  output_string ide_support (String.concat "\n" !cc_args);
  output_char ide_support '\n';
  close_out ide_support;

  files @ extra_c_files

(** All the [.o] files thus obtained and all the [.o] files passed on the
 * command-line are linked together; any [-o] option is passed to the final
 * invocation of [gcc]. *)
let link c_files o_files =
  let o_files = List.map expand_prefixes o_files in
  let objects = List.map o_of_c c_files @ o_files @
    [ !krmllib_dir ^^ "dist" ^^ "generic" ^^ "libkrmllib.a" ]
  in
  let extra_arg = if !Options.exe_name <> "" then Dash.o_exe !Options.exe_name else [] in
  if run_or_warn "[LD]" !cc (!cc_args @ objects @ extra_arg @ List.rev !Options.ldopts) then begin
    if not !Options.silent then
      KPrint.bprintf "%sAll files linked successfully%s 👍\n" Ansi.green Ansi.reset
  end else begin
    KPrint.bprintf "%s%s failed at the final linking phase%s\n" Ansi.red !Options.cc Ansi.reset;
    exit 250
  end
