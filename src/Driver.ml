(** A very boring module that detects the environment and figures out how to
 * call the tools. *)

open Warnings

module Dash = struct
  let i dir =
    if !Options.cc = "msvc" then
      [ "/I"; dir ]
    else
      [ "-I"; dir ]

  let c file =
    if !Options.cc = "msvc" then
      [ "/c"; file ]
    else
      [ "-c"; file ]

  let d opt =
    if !Options.cc = "msvc" then
      "/D" ^ opt
    else
      "-D" ^ opt

  let o_obj file =
    if !Options.cc = "msvc" then
      [ "/Fo:"; file ]
    else
      [ "-o"; file ]

  let o_exe file =
    if !Options.cc = "msvc" then
      [ "/Fe:"; file ]
    else
      [ "-o"; file ]
end


module P = Process
(* Note: don't open [Process], otherwise any reference to [Output] will be
 * understood as a cyclic dependency on our own [Output] module. *)

(** These three variables filled in by [detect_fstar] *)
let fstar = ref ""
let fstar_home = ref ""
let fstar_lib = ref ""
let fstar_options = ref []

(** By [detect_kremlin] *)
let krml_home = ref ""

(** These two filled in by [detect_gcc] and others *)
let cc = ref ""
let cc_args = ref []

(** The base tools *)
let readlink = ref ""

(* All our paths use "/" as a separator, INCLUDING windows paths because
 * they're run through cygpath -m *)
let (^^) x y = x ^ "/" ^ y

let d = Filename.dirname

let rec mkdirp d =
  if Sys.file_exists d then begin
    if not (Sys.is_directory d) then
      failwith "mkdirp: not a directory"
  end else begin
    mkdirp (Filename.dirname d);
    Unix.mkdir d 0o755
  end

let mk_tmpdir_if () =
  if !Options.tmpdir <> "" then
    mkdirp !Options.tmpdir

(** Check whether a command exited successfully *)
let success cmd args =
  match Process.run cmd args with
  | { Process.Output.exit_status = Process.Exit.Exit 0; _ } -> true
  | _ -> false

let read_one_line cmd args =
  String.trim (List.hd (Process.read_stdout cmd args))

let read_one_error_line cmd args =
  match Process.run cmd args with
  | { Process.Output.stderr; _ } ->
      String.trim (List.hd stderr)

(** The tools we depend on; namely, readlink. *)
let detect_base_tools () =
  KPrint.bprintf "%s⚙ KreMLin auto-detecting tools.%s Here's what we found:\n" Ansi.blue Ansi.reset;

  if success "which" [| "greadlink" |] then
    readlink := "greadlink"
  else
    readlink := "readlink";
  begin try
    if read_one_line "uname" [||] = "Darwin" && !readlink = "readlink" then
      KPrint.bprintf "Warning: OSX detected and no greadlink found. Suggestion: \
        [brew install coreutils]\n";
  with Process.Exit.Error _ ->
    ()
  end;
  KPrint.bprintf "%sreadlink is:%s %s\n" Ansi.underline Ansi.reset !readlink

let detect_base_tools_if () =
  if !readlink = "" then
    detect_base_tools ()


(** Fills in krml_home, and prepends the path to [kremlib] to [Options.includes] *)
let detect_kremlin () =
  detect_base_tools_if ();

  KPrint.bprintf "%sKreMLin called via:%s %s\n" Ansi.underline Ansi.reset Sys.argv.(0);

  let real_krml =
    let me = Sys.argv.(0) in
    if Sys.os_type = "Win32" && not (Filename.is_relative me) then
      me
    else
      try read_one_line !readlink [| "-f"; read_one_line "which" [| me |] |]
      with _ -> fatal_error "Could not compute full krml path"
  in
  (* ../_build/src/Kremlin.native *)
  KPrint.bprintf "%sthe Kremlin executable is:%s %s\n" Ansi.underline Ansi.reset real_krml;

  let home =
    try read_one_line !readlink [| "-f"; d real_krml ^^ ".." ^^ ".." |]
    with _ -> fatal_error "Could not compute krml_home"
  in
  KPrint.bprintf "%sKreMLin home is:%s %s\n" Ansi.underline Ansi.reset home;
  krml_home := home;

  Options.includes := (!krml_home ^^ "kremlib") :: !Options.includes

let detect_kremlin_if () =
  if !krml_home = "" then
    detect_kremlin ()

let expand_fstar_home fstar_home fstar_lib s =
  if KString.starts_with s "FSTAR_LIB" then
    fstar_lib ^^ KString.chop s "FSTAR_LIB"
  else if KString.starts_with s "FSTAR_HOME" then
    fstar_home ^^ KString.chop s "FSTAR_HOME"
  else
    s

(* Fills in fstar{,_home,_options} *)
let detect_fstar () =
  detect_kremlin_if ();

  KPrint.bprintf "%s⚙ KreMLin will drive F*.%s Here's what we found:\n" Ansi.blue Ansi.reset;

  begin try
    let r = Sys.getenv "FSTAR_HOME" in
    KPrint.bprintf "read FSTAR_HOME via the environment\n";
    fstar_home := r;
    fstar := r ^^ "bin" ^^ "fstar.exe"
  with Not_found -> try
    fstar := read_one_line "which" [| "fstar.exe" |];
    fstar_home := d (d !fstar);
    KPrint.bprintf "FSTAR_HOME is %s (via fstar.exe in PATH)\n" !fstar_home
  with _ ->
    fatal_error "Did not find fstar.exe in PATH and FSTAR_HOME is not set"
  end;

  if KString.exists !fstar_home "opam"; then begin
    KPrint.bprintf "Detected an OPAM setup of F*\n";
    fstar_lib := !fstar_home ^^ "lib" ^^ "fstar"
  end else begin
    fstar_lib := !fstar_home ^^ "ulib"
  end;

  if success "which" [| "cygpath" |] then begin
    fstar := read_one_line "cygpath" [| "-m"; !fstar |];
    KPrint.bprintf "%sfstar converted to windows path:%s %s\n" Ansi.underline Ansi.reset !fstar;
    fstar_home := read_one_line "cygpath" [| "-m"; !fstar_home |];
    KPrint.bprintf "%sfstar home converted to windows path:%s %s\n" Ansi.underline Ansi.reset !fstar_home;
    fstar_lib := read_one_line "cygpath" [| "-m"; !fstar_lib |];
    KPrint.bprintf "%sfstar lib converted to windows path:%s %s\n" Ansi.underline Ansi.reset !fstar_lib
  end;

  if try Sys.is_directory (!fstar_home ^^ ".git") with Sys_error _ -> false then begin
    let cwd = Sys.getcwd () in
    Sys.chdir !fstar_home;
    let branch = read_one_line "git" [| "rev-parse"; "--abbrev-ref"; "HEAD" |] in
    let color = if branch = "master" then Ansi.green else Ansi.orange in
    KPrint.bprintf "fstar is on %sbranch %s%s\n" color branch Ansi.reset;
    Sys.chdir cwd
  end;

  (* Add default include directories, those specified by the user, and skip a
   * set of known failing modules. Adding a new module to the failing list is
   * DANGEROUS: it will remove a bunch of [DExternal] declarations that the
   * type-checker needs! *)
  let fstar_includes = List.map (expand_fstar_home !fstar_home !fstar_lib) !Options.includes in
  fstar_options := [
    "--trace_error";
  ] @ List.flatten (List.rev_map (fun d -> ["--include"; d]) fstar_includes);
  (** We don't even try to extract the int modules, because Kremlin cannot
   * type-check them, as it assumes a primitive notion of integers... see also
   * [Options.drop] for modules that we're happy to let F* extract (for
   * typing), but don't want to generate C for. *)
  let record_no_extract m =
    fstar_options := "--no_extract" :: ("FStar." ^ m) :: !fstar_options
  in
  List.iter record_no_extract
    [ "Int8"; "UInt8"; "Int16"; "UInt16"; "Int31"; "UInt31"; "Int32"; "UInt32";
      "Int63"; "UInt63"; "Int64"; "UInt64"; "Int128"; "Seq.Base"; "HyperStack.ST";
      "HyperStack"; "HyperHeap"; "Math.Lib"; "Map"; "Monotonic.HyperHeap"; "Buffer";
      "Monotonic.HyperStack" ];
  if not !Options.uint128 then
    fstar_options := (!fstar_home ^^ "ulib" ^^ "FStar.UInt128.fst") :: !fstar_options;
  if !Options.wasm then
    fstar_options := (!krml_home ^^ "runtime" ^^ "WasmSupport.fst") :: !fstar_options;
  KPrint.bprintf "%sfstar is:%s %s %s\n" Ansi.underline Ansi.reset !fstar (String.concat " " !fstar_options);

  flush stdout

let detect_fstar_if () =
  if !fstar = "" then
    detect_fstar ()

let expand_fstar_home s =
  detect_fstar_if ();
  expand_fstar_home !fstar_home !fstar_lib s

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
      KPrint.bprintf "%s✔%s %s%s\n" Ansi.green Ansi.reset str (verbose_msg ());
      if !Options.verbose then
        List.iter print_endline stdout;
        List.iter print_endline stderr;
      true
  | { P.Output.stderr; stdout; _ } ->
      KPrint.bprintf "%s✘%s %s%s\n" Ansi.red Ansi.reset str (verbose_msg ());
      List.iter print_endline stderr;
      List.iter print_endline stdout;
      Pervasives.(flush stdout; flush stderr);
      maybe_fatal_error ("run_or_warn", ExternalError debug_str);
      false

(** Called from the top-level file; runs [fstar] on the [.fst] files
 * passed on the command-line, and returns the name of the generated file. *)
let run_fstar verify skip_extract skip_translate files =
  assert (List.length files > 0);
  detect_fstar_if ();

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
      "--codegen" :: "Kremlin" ::
      "--lax" :: args
    in
    flush stdout;
    mk_tmpdir_if ();
    if not (run_or_warn "[F*,extract]" !fstar args) then
      fatal_error "F* failed";
    if skip_translate then
      exit 0;
    !Options.tmpdir ^^ "out.krml"

let detect_gnu flavor =
  KPrint.bprintf "%s⚙ KreMLin will drive the C compiler.%s Here's what we found:\n" Ansi.blue Ansi.reset;
  let rec search = function
    | fmt :: rest ->
        let cmd = KPrint.bsprintf fmt flavor in
        if success "which" [| cmd |] then
          cc := cmd
        else
          search rest
    | [] ->
        Warnings.fatal_error "gcc not found in path!";
  in
  let crosscc = if !Options.m32 then format_of_string "i686-w64-mingw32-%s" else format_of_string "x86_64-w64-mingw32-%s" in
  search [ "%s-7"; "%s-6"; "%s-5"; crosscc; "%s" ];

  KPrint.bprintf "%sgcc is:%s %s\n" Ansi.underline Ansi.reset !cc;

  if !Options.m32 then
    cc_args := "-m32" :: !cc_args;
  KPrint.bprintf "%s%s options are:%s %s\n" Ansi.underline !cc Ansi.reset
    (String.concat " " !cc_args)


let detect_compcert () =
  if success "which" [| "ccomp" |] then
    cc := "ccomp"
  else
    Warnings.fatal_error "ccomp not found in path!"


let fill_cc_args () =
  (** For the side-effect of filling in [Options.include] *)
  detect_kremlin_if ();

  cc_args :=
      (if not !Options.uint128 then [ Dash.d "KRML_NOUINT128" ] else [])
    @ (if not !Options.struct_passing then [ Dash.d "KRML_NOSTRUCT_PASSING" ] else [])
    @ List.flatten (List.rev_map Dash.i (!Options.tmpdir :: !Options.includes))
    @ List.rev !Options.ccopts
    @ !cc_args


let detect_cc_if () =
  fill_cc_args ();
  if !cc = "" then
    match !Options.cc with
    | "gcc" ->
        detect_gnu "gcc"
    | "compcert" ->
        detect_compcert ()
    | "g++" ->
        detect_gnu "g++"
    | "clang" ->
        detect_gnu "clang"
    | "msvc" ->
        cc := !krml_home ^^ "misc" ^^ "cl-wrapper.bat";
    | _ ->
        fatal_error "Unrecognized value for -cc: %s" !Options.cc

let o_of_c f =
  let dot_o = if !Options.cc = "msvc" then ".obj" else ".o" in
  !Options.tmpdir ^^ Filename.chop_suffix (Filename.basename f) ".c" ^ dot_o


(** For "kremlib.c", and every [.c] file generated by Kremlin or passed on the
 * command-line, run [gcc -c] to obtain a [.o]. Files that don't compile are
 * silently dropped, or KreMLin aborts if warning 3 is fatal. *)
let compile files extra_c_files =
  assert (List.length files > 0);
  let extra_c_files = List.map expand_fstar_home extra_c_files in
  detect_kremlin_if ();
  detect_cc_if ();
  flush stdout;
  let extra_c_files = (!krml_home ^^ "kremlib" ^^ "kremlib.c") :: extra_c_files in

  let files = List.map (fun f -> !Options.tmpdir ^^ f ^ ".c") files in
  KPrint.bprintf "%s⚡ Generating object files%s\n" Ansi.blue Ansi.reset;
  let gcc_c file =
    flush stdout;
    let info = Printf.sprintf "[CC,%s]" file in
    run_or_warn info !cc (!cc_args @ Dash.c file @ Dash.o_obj (o_of_c file))
  in
  let files = List.filter gcc_c files in
  let extra_c_files = List.filter gcc_c extra_c_files in
  files @ extra_c_files

(** All the [.o] files thus obtained and all the [.o] files passed on the
 * command-line are linked together; any [-o] option is passed to the final
 * invocation of [gcc]. *)
let link c_files o_files =
  let o_files = List.map expand_fstar_home o_files in
  let objects = List.map o_of_c c_files @ o_files in
  let extra_arg = if !Options.exe_name <> "" then Dash.o_exe !Options.exe_name else [] in
  if run_or_warn "[LD]" !cc (!cc_args @ objects @ extra_arg @ List.rev !Options.ldopts) then
    KPrint.bprintf "%sAll files linked successfully%s 👍\n" Ansi.green Ansi.reset
  else begin
    KPrint.bprintf "%s%s failed at the final linking phase%s\n" Ansi.red !Options.cc Ansi.reset;
    exit 250
  end
