(** A very boring module that detects the environment and figures out how to
 * call the tools. *)

open Warnings

let fstar = ref ""
let fstar_home = ref ""
let fstar_options = ref []
let krml_home = ref ""
let gcc = ref ""
let gcc_args = ref []

let (^^) x y = x ^ "/" ^ y
let d = Filename.dirname

let success cmd args =
  match Process.run cmd args with
  | { Process.Output.exit_status = Process.Exit.Exit 0; _ } -> true
  | _ -> false

let detect_fstar () =
  KPrint.bprintf "%sKreMLin will drive F*.%s Here's what we found:\n" Ansi.blue Ansi.reset;
  KPrint.bprintf "%sKreMLin called via:%s %s\n" Ansi.underline Ansi.reset Sys.argv.(0);

  (* All our paths use "/" as a separator, INCLUDING windows paths because
   * they're run through cygpath -m *)

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
    if not (Filename.is_relative me) then
      me
    else if try ignore (String.index me '/'); true with Not_found -> false then
      Sys.getcwd () ^^ me
    else
      let f =
        try read_one_line "which" [| Sys.argv.(0) |]
        with _ -> fatal_error "Could not compute full krml path (which)"
      in
      try read_one_line readlink [| "-f"; f |]
      with _ -> fatal_error "Could not compute full krml path (readlink)"
  in
  (* ../_build/src/Kremlin.native *)
  KPrint.bprintf "%sthe Kremlin executable is:%s %s\n" Ansi.underline Ansi.reset real_krml;

  let home = d real_krml ^^ ".." ^^ ".." in
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

  let fstar_includes = [
    !fstar_home ^^ "examples" ^^ "low-level";
    !fstar_home ^^ "examples" ^^ "low-level" ^^ "crypto";
    !krml_home ^^ "kremlib"
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

let run_fstar files =
  assert (List.length files > 0);
  detect_fstar_if ();

  let args = !fstar_options @ files in
  KPrint.bprintf "%sCalling F*%s\n" Ansi.blue Ansi.reset;
  flush stdout;
  if not (run_or_warn "[fstar,extract]" !fstar args) then
    fatal_error "F* failed";
  "out.krml"

let detect_gcc () =
  KPrint.bprintf "%sKreMLin will drive the C compiler.%s Here's what we found:\n" Ansi.blue Ansi.reset;
  if success "which" [| "gcc-5" |] then
    gcc := "gcc-5"
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
    "-std=c11"
  ] @ List.flatten (List.rev_map (fun d -> ["-I"; d]) (!Options.tmpdir :: !Options.includes));
  KPrint.bprintf "%sgcc options are:%s %s\n" Ansi.underline Ansi.reset
    (String.concat " " !gcc_args)

let detect_gcc_if () =
  if !gcc = "" then
    detect_gcc ()

let compile_and_link files c_files o_files =
  assert (List.length files > 0);
  detect_gcc_if ();
  flush stdout;

  let files = List.map (fun f -> !Options.tmpdir ^^ f ^ ".c") files in
  KPrint.bprintf "%sGenerating object files%s\n" Ansi.blue Ansi.reset;
  let gcc_c file =
    flush stdout;
    let info = Printf.sprintf "[gcc,compile,%s]" file in
    run_or_warn info !gcc (!gcc_args @ [ "-c"; file ])
  in
  let files = List.filter gcc_c files in
  let c_files = List.filter gcc_c c_files in

  let o_of_c f = Filename.chop_suffix f ".c" ^ ".o" in
  let objects = List.map o_of_c files @
    List.map o_of_c c_files @
    o_files
  in
  if run_or_warn "[gcc,link]" !gcc (!gcc_args @ objects) then
    KPrint.bprintf "%sAll files linked successfully%s 👍" Ansi.green Ansi.reset
  else
    KPrint.bprintf "%sgcc failed at the final linking phase%s\n" Ansi.red Ansi.reset
