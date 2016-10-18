(** A very boring module that detects the environment and figures out how to
 * call the tools. *)

open Warnings

module P = Process
(* Note: don't open [Process], otherwise any reference to [Output] will be
 * understood as a cyclic dependency on our own [Output] module. *)

(** These three variables filled in by [detect_fstar] *)
let fstar = ref ""
let fstar_home = ref ""
let fstar_options = ref []

(** By [detect_kremlin] *)
let krml_home = ref ""

(** These two filled in by [detect_gcc] *)
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

let expand_fstar_home s =
  let s' = "FSTAR_HOME" in
  let l = String.length s in
  let l' = String.length s' in
  if l >= l' && String.sub s 0 (String.length s') = s' then
    !fstar_home ^ String.sub s l' (l - l')
  else
    s

(** The tools we depend on; namely, readlink. *)
let detect_base_tools () =
  KPrint.bprintf "%s⚙ KreMLin auto-detecting tools.%s Here's what we found:\n" Ansi.blue Ansi.reset;

  if success "which" [| "greadlink" |] then
    readlink := "greadlink"
  else
    readlink := "readlink";
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


(** Fills in fstar{,_home,_options} *)
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
    fstar_home := d (d !fstar)
  with _ ->
    fatal_error "Did not find fstar.exe in PATH and FSTAR_HOME is not set"
  end;

  if success "which" [| "cygpath" |] then begin
    fstar := read_one_line "cygpath" [| "-m"; !fstar |];
    KPrint.bprintf "%sfstar converted to windows path:%s %s\n" Ansi.underline Ansi.reset !fstar;
    fstar_home := read_one_line "cygpath" [| "-m"; !fstar_home |];
    KPrint.bprintf "%sfstar home converted to windows path:%s %s\n" Ansi.underline Ansi.reset !fstar_home
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
   * set of known failing modules. *)
  let fstar_includes = List.map expand_fstar_home !Options.includes in
  fstar_options := [
    "--trace_error";
  ] @ List.flatten (List.rev_map (fun d -> ["--include"; d]) fstar_includes);
  List.iter (fun m ->
    fstar_options := "--no_extract" :: ("FStar." ^ m) :: !fstar_options
  ) [ "Int8"; "UInt8"; "Int16"; "UInt16"; "Int31"; "UInt31"; "Int32"; "UInt32";
      "Int63"; "UInt63"; "Int64"; "UInt64"; "Int128"; "UInt128";
      "HyperStack"; "HST" ];
  KPrint.bprintf "%sfstar is:%s %s %s\n" Ansi.underline Ansi.reset !fstar (String.concat " " !fstar_options);

  flush stdout

let detect_fstar_if () =
  if !fstar = "" then
    detect_fstar ()

let verbose_msg () =
  if !Options.verbose then
    ""
  else
    " (use -verbose to see the output)"

(** Run a command, print its output if [-verbose] is passed, and possibly abort
 * (depending on -warn-error) if the command failed. *)
let run_or_warn str exe args =
  let debug_str = KPrint.bsprintf "%s %s" exe (String.concat " " args) in
  match P.run exe (Array.of_list args) with
  | { P.Output.exit_status = P.Exit.Exit 0; stdout; _ } ->
      KPrint.bprintf "%s✔%s %s%s\n" Ansi.green Ansi.reset str (verbose_msg ());
      if !Options.verbose then
        List.iter print_endline stdout;
      true
  | { P.Output.stderr; stdout; _ } ->
      KPrint.bprintf "%s✘%s %s%s\n" Ansi.red Ansi.reset str (verbose_msg ());
      if !Options.verbose then begin
        List.iter print_endline stderr;
        List.iter print_endline stdout
      end;
      maybe_fatal_error ("run_or_warn", ExternalError debug_str);
      Pervasives.(flush stdout; flush stderr);
      false

(** Called from the top-level file; runs [fstar] on the [.fst] files
 * passed on the command-line, and returns the name of the generated file. *)
let run_fstar verify skip_extract files =
  assert (List.length files > 0);
  detect_fstar_if ();

  KPrint.bprintf "%s⚡ Calling F*%s\n" Ansi.blue Ansi.reset;
  let args = List.rev !Options.fsopts @ !fstar_options @ files in
  if verify then begin
    flush stdout;
    if not (run_or_warn "[F*,verify]" !fstar args) then
      fatal_error "F* failed"
  end;

  if skip_extract then
    exit 0
  else
    let args =
      "--odir" :: !Options.tmpdir ::
      "--codegen" :: "Kremlin" ::
      "--lax" :: !fstar_options @ files
    in
    flush stdout;
    mk_tmpdir_if ();
    if not (run_or_warn "[F*,extract]" !fstar args) then
      fatal_error "F* failed";
    !Options.tmpdir ^^ "out.krml"

(** Fills in [cc] and [cc_args]. *)
let detect_gnu flavor =
  (** For the side-effect of filling in [Options.include] *)
  detect_kremlin_if ();

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
  search [ "%s-5"; "%s-6"; "x86_64-w64-mingw32-%s"; "%s" ];

  KPrint.bprintf "%sgcc is:%s %s\n" Ansi.underline Ansi.reset !cc;

  cc_args := [
    "-Wall";
    "-Werror";
    "-Wno-parentheses";
    "-Wno-unused-variable";
    "-g";
    "-O3";
    "-fwrapv"
  ] @ List.flatten (List.rev_map (fun d -> ["-I"; d]) (!Options.tmpdir :: !Options.includes))
    @ List.rev !Options.ccopts;
  KPrint.bprintf "%s%s options are:%s %s\n" Ansi.underline !cc Ansi.reset
    (String.concat " " !cc_args)

let detect_gcc () =
  detect_gnu "gcc";
  cc_args := "-Wno-unused-but-set-variable" :: "-std=c11" :: !cc_args

let detect_gpp () =
  detect_gnu "g++";
  cc_args := "-Wno-unused-but-set-variable" :: !cc_args

let detect_clang () =
  detect_gnu "clang"

let detect_compcert () =
  if success "which" [| "ccomp" |] then
    cc := "ccomp"
  else
    Warnings.fatal_error "ccomp not found in path!";

  cc_args := [
    "-g";
    "-O3";
    "-fstruct-passing"
  ] @ List.flatten (List.rev_map (fun d -> ["-I"; d]) (!Options.tmpdir :: !Options.includes))
    @ List.rev !Options.ccopts


let detect_cc_if () =
  if !cc = "" then
    match !Options.cc with
    | "gcc" ->
        detect_gcc ()
    | "compcert" ->
        detect_compcert ()
    | "g++" ->
        detect_gpp ()
    | "clang" ->
        detect_clang ()
    | _ ->
        fatal_error "Unrecognized value for -cc: %s" !Options.cc

let o_of_c f =
  !Options.tmpdir ^^ Filename.chop_suffix (Filename.basename f) ".c" ^ ".o"

(** For "kremlib.c", and every [.c] file generated by Kremlin or passed on the
 * command-line, run [gcc -c] to obtain a [.o]. Files that don't compile are
 * silently dropped, or KreMLin aborts if warning 3 is fatal. *)
let compile files extra_c_files =
  assert (List.length files > 0);
  detect_kremlin_if ();
  detect_cc_if ();
  flush stdout;
  let extra_c_files = (!krml_home ^^ "kremlib" ^^ "kremlib.c") :: extra_c_files in

  let files = List.map (fun f -> !Options.tmpdir ^^ f ^ ".c") files in
  KPrint.bprintf "%s⚡ Generating object files%s\n" Ansi.blue Ansi.reset;
  let gcc_c file =
    flush stdout;
    let info = Printf.sprintf "[CC,%s]" file in
    run_or_warn info !cc (!cc_args @ [ "-c"; file; "-o"; o_of_c file ])
  in
  let files = List.filter gcc_c files in
  let extra_c_files = List.filter gcc_c extra_c_files in
  files @ extra_c_files

(** All the [.o] files thus obtained and all the [.o] files passed on the
 * command-line are linked together; any [-o] option is passed to the final
 * invocation of [gcc]. *)
let link c_files o_files =
  let objects = List.map o_of_c c_files @ o_files in
  let extra_arg = if !Options.exe_name <> "" then [ "-o"; !Options.exe_name ] else [] in
  if run_or_warn "[LD]" !cc (!cc_args @ objects @ extra_arg @ List.rev !Options.ldopts) then
    KPrint.bprintf "%sAll files linked successfully%s 👍\n" Ansi.green Ansi.reset
  else begin
    KPrint.bprintf "%sgcc failed at the final linking phase%s\n" Ansi.red Ansi.reset;
    exit 250
  end
