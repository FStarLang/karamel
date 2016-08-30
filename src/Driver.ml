open Warnings

let fstar = ref ""
let fstar_home = ref ""
let fstar_options = ref []
let krml_home = ref ""

let detect_fstar () =
  KPrint.bprintf "%sKreMLin will drive F*.%s Here's what we found:\n" Ansi.blue Ansi.reset;
  KPrint.bprintf "%sKreMLin called via:%s %s\n" Ansi.underline Ansi.reset Sys.argv.(0);

  (* All our paths use "/" as a separator, INCLUDING windows paths because
   * they're run through cygpath -m *)
  let (^^) x y = x ^ "/" ^ y  in
  let d = Filename.dirname in

  let success cmd args =
    match Utils.run cmd args with
    | Unix.WEXITED 0, _, _ -> true
    | _ -> false
  in

  let readlink =
    if success "which" [| "greadlink" |] then
      "greadlink"
    else
      "readlink"
  in
  KPrint.bprintf "%sreadlink is:%s %s\n" Ansi.underline Ansi.reset readlink;

  let real_krml =
    let me = Sys.argv.(0) in
    if not (Filename.is_relative me) then
      me
    else if try ignore (String.index me '/'); true with Not_found -> false then
      Sys.getcwd () ^^ me
    else
      let f =
        try String.trim (Utils.run_and_read "which" [| Sys.argv.(0) |])
        with _ -> fatal_error "Could not compute full krml path (which)"
      in
      try String.trim (Utils.run_and_read readlink [| "-f"; f |])
      with _ -> fatal_error "Could not compute full krml path (readlink)"
  in
  (* ../_build/src/Kremlin.native *)
  KPrint.bprintf "%sthe Kremlin executable is:%s %s\n" Ansi.underline Ansi.reset real_krml;

  let home = d real_krml ^^ ".." ^^ ".." in
  KPrint.bprintf "%sKreMLin home is:%s %s\n" Ansi.underline Ansi.reset home;
  krml_home := home;

  let output =
    try String.trim (Utils.run_and_read "which" [| "fstar.exe" |])
    with e -> Printexc.print_backtrace stdout; print_endline (Printexc.to_string e); raise e
  in
  KPrint.bprintf "%sfstar is:%s %s\n" Ansi.underline Ansi.reset output;
  fstar := output;

  let home = d (d !fstar) in
  KPrint.bprintf "%sfstar home is:%s %s\n" Ansi.underline Ansi.reset home;
  fstar_home := home;

  if success "which" [| "cygpath" |] then begin
    fstar := String.trim (Utils.run_and_read "cygpath" [| "-m"; !fstar |]);
    KPrint.bprintf "%sfstar converted to windows path:%s %s\n" Ansi.underline Ansi.reset !fstar;
    fstar_home := String.trim (Utils.run_and_read "cygpath" [| "-m"; !fstar_home |]);
    KPrint.bprintf "%sfstar home converted to windows path:%s %s\n" Ansi.underline Ansi.reset !fstar_home
  end;

  let fstar_includes = [
    !fstar_home ^^ "examples" ^^ "low-level";
    !fstar_home ^^ "examples" ^^ "low-level" ^^ "crypto";
    !krml_home ^^ "kremlib"
  ] in
  fstar_options := [
    "--lax"; "--trace_error"; "--codegen"; "Kremlin"
  ] @ List.flatten (List.map (fun d -> ["--include"; d]) fstar_includes);
  KPrint.bprintf "%sfstar is:%s %s %s\n" Ansi.underline Ansi.reset !fstar (String.concat " " !fstar_options);

  flush stdout

let detect_fstar_if () =
  if !fstar = "" then
    detect_fstar ()

let verbose_msg () =
  if !Options.verbose then ""
  else " (use -verbose to see the output)"

let run_fstar files =
  assert (List.length files > 0);
  detect_fstar_if ();

  let args = !fstar_options @ files in
  KPrint.bprintf "%sCalling F*%s\n" Ansi.blue Ansi.reset;
  flush stdout;
  match Utils.run !fstar (Array.of_list args) with
  | Unix.WEXITED 0, stdout, _ ->
      KPrint.bprintf "%sfstar exited normally%s%s\n" Ansi.green Ansi.reset (verbose_msg ());
      if !Options.verbose then
        print_string stdout;
      "out.krml"
  | _, _, stderr ->
      KPrint.bprintf "%sfstar exited abnormally!%s\n" Ansi.red Ansi.reset;
      print_string stderr;
      exit 252
