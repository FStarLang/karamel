(** A very boring module that detects the environment and figures out how to
 * call the tools. *)

open Warnings

(** These four variables filled in by [detect_fstar] *)
let fstar = ref ""
let fstar_home = ref ""
let fstar_options = ref []
let krml_home = ref ""

(** These two filled in by [detect_gcc] *)
let gcc = ref ""
let gcc_args = ref []

(* All our paths use "/" as a separator, INCLUDING windows paths because
 * they're run through cygpath -m *)
let (^^) x y = x ^ "/" ^ y

let d = Filename.dirname

(** Check whether a command exited successfully *)
let success cmd args =
  match Process.run cmd args with
  | { Process.Output.exit_status = Process.Exit.Exit 0; _ } -> true
  | _ -> false

(** Fills in fstar{,_home,_options} and krml_home, and prepends the path to
 * [kremlib] to [Options.includes] *)
let detect_fstar () =
  KPrint.bprintf "%sKreMLin will drive F*.%s Here's what we found:\n" Ansi.blue Ansi.reset;
  KPrint.bprintf "%sKreMLin called via:%s %s\n" Ansi.underline Ansi.reset Sys.argv.(0);

  let readlink =
    if success "which" [| "greadlink" |] then
      "greadlink"
    else
      "readlink"
  in
  KPrint.bprintf "%sreadlink is:%s %s\n" Ansi.underline Ansi.reset readlink;

  let read_one_line cmd args =
    String.trim (List.hd (Process.read_stdout cmd args))
  in

  let real_krml =
    let me = Sys.argv.(0) in
    if Sys.os_type = "Win32" && not (Filename.is_relative me) then
      me
    else
      try read_one_line readlink [| "-f"; read_one_line "which" [| me |] |]
      with _ -> fatal_error "Could not compute full krml path"
  in
  (* ../_build/src/Kremlin.native *)
  KPrint.bprintf "%sthe Kremlin executable is:%s %s\n" Ansi.underline Ansi.reset real_krml;

  let home =
    try read_one_line readlink [| "-f"; d real_krml ^^ ".." ^^ ".." |]
    with _ -> fatal_error "Could not compute krml_home"
  in
  KPrint.bprintf "%sKreMLin home is:%s %s\n" Ansi.underline Ansi.reset home;
  krml_home := home;

  let output =
    try read_one_line "which" [| "fstar.exe" |]
    with e -> Printexc.print_backtrace stdout; print_endline (Printexc.to_string e); raise e
  in
  KPrint.bprintf "%sfstar is:%s %s\n" Ansi.underline Ansi.reset output;
  fstar := output;

  let home = d (d !fstar) in
  KPrint.bprintf "%sfstar home is:%s %s\n" Ansi.underline Ansi.reset home;
  fstar_home := home;

  if success "which" [| "cygpath" |] then begin
    fstar := read_one_line "cygpath" [| "-m"; !fstar |];
    KPrint.bprintf "%sfstar converted to windows path:%s %s\n" Ansi.underline Ansi.reset !fstar;
    fstar_home := read_one_line "cygpath" [| "-m"; !fstar_home |];
    KPrint.bprintf "%sfstar home converted to windows path:%s %s\n" Ansi.underline Ansi.reset !fstar_home
  end;

  (** Note: adding [kremlib/] as a default include path. *)
  Options.includes := (!krml_home ^^ "kremlib") :: !Options.includes;

  let fstar_includes = [
    !fstar_home ^^ "examples" ^^ "low-level";
    !fstar_home ^^ "examples" ^^ "low-level" ^^ "crypto";
  ] @ !Options.includes in
  fstar_options := [
    "--lax"; "--trace_error"; "--codegen"; "Kremlin"
  ] @ List.flatten (List.rev_map (fun d -> ["--include"; d]) fstar_includes);
  KPrint.bprintf "%sfstar is:%s %s %s\n" Ansi.underline Ansi.reset !fstar (String.concat " " !fstar_options);

  flush stdout

let detect_fstar_if () =
  if !fstar = "" then
    detect_fstar ()

let verbose_msg () =
  if !Options.verbose then ""
  else " (use -verbose to see the output)"

(** Run a command, print its output if [-verbose] is passed, and possibly abort
 * (depending on -warn-error) if the command failed. *)
let run_or_warn str exe args =
  let debug_str = KPrint.bsprintf "%s %s" exe (String.concat " " args) in
  if !Options.verbose then
    print_endline debug_str;
  let open Process in
  match run exe (Array.of_list args) with
  | { Output.exit_status = Exit.Exit 0; stdout; _ } ->
      KPrint.bprintf "%s✔%s %s%s\n" Ansi.green Ansi.reset str (verbose_msg ());
      if !Options.verbose then
        List.iter print_endline stdout;
      true
  | { Output.stderr = err; _ } ->
      KPrint.bprintf "%s✘%s %s%s\n" Ansi.red Ansi.reset str (verbose_msg ());
      if !Options.verbose then
        List.iter print_endline err;
      maybe_raise_error ("run_or_warn", ExternalError debug_str);
      flush stderr;
      false

(** Called from the top-level file; runs [fstar] on the [.fst] files
 * passed on the command-line, and returns the name of the generated file. *)
let run_fstar files =
  assert (List.length files > 0);
  detect_fstar_if ();

  let args = !fstar_options @ files in
  KPrint.bprintf "%sCalling F*%s\n" Ansi.blue Ansi.reset;
  flush stdout;
  if not (run_or_warn "[fstar,extract]" !fstar args) then
    fatal_error "F* failed";
  "out.krml"

(** Fills in [gcc] and [gcc_args]. *)
let detect_gcc () =
  KPrint.bprintf "%sKreMLin will drive the C compiler.%s Here's what we found:\n" Ansi.blue Ansi.reset;
  if success "which" [| "gcc-5" |] then
    gcc := "gcc-5"
  else if success "which" [| "gcc-6" |] then
    gcc := "gcc-6"
  else if success "which" [| "x86_64-w64-mingw32-gcc" |] then
    gcc := "x86_64-w64-mingw32-gcc"
  else if success "which" [| "gcc" |] then
    gcc := "gcc"
  else
    Warnings.fatal_error "gcc not found in path!";
  KPrint.bprintf "%sgcc is:%s %s\n" Ansi.underline Ansi.reset !gcc;

  gcc_args := [
    "-Wall";
    "-Werror";
    "-Wno-parentheses";
    "-Wno-unused-variable";
    "-Wno-unused-but-set-variable";
    "-std=c11"
  ] @ List.flatten (List.rev_map (fun d -> ["-I"; d]) (!Options.tmpdir :: !Options.includes));
  KPrint.bprintf "%sgcc options are:%s %s\n" Ansi.underline Ansi.reset
    (String.concat " " !gcc_args)

let detect_gcc_if () =
  if !gcc = "" then
    detect_gcc ()

let o_of_c f =
  !Options.tmpdir ^^ Filename.chop_suffix (Filename.basename f) ".c" ^ ".o"

(** For "kremlib.c", and every [.c] file generated by Kremlin or passed on the
 * command-line, run [gcc -c] to obtain a [.o]. Files that don't compile are
 * silently dropped, or KreMLin aborts if warning 3 is fatal. *)
let compile files extra_c_files =
  assert (List.length files > 0);
  detect_fstar_if ();
  detect_gcc_if ();
  flush stdout;
  let extra_c_files = (!krml_home ^^ "kremlib" ^^ "kremlib.c") :: extra_c_files in

  let files = List.map (fun f -> !Options.tmpdir ^^ f ^ ".c") files in
  KPrint.bprintf "%sGenerating object files%s\n" Ansi.blue Ansi.reset;
  let gcc_c file =
    flush stdout;
    let info = Printf.sprintf "[gcc,compile,%s]" file in
    run_or_warn info !gcc (!gcc_args @ [ "-c"; file; "-o"; o_of_c file ])
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
  if run_or_warn "[gcc,link]" !gcc (!gcc_args @ objects @ extra_arg) then
    KPrint.bprintf "%sAll files linked successfully%s 👍\n" Ansi.green Ansi.reset
  else
    KPrint.bprintf "%sgcc failed at the final linking phase%s\n" Ansi.red Ansi.reset
