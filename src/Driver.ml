open Warnings

let fstar = ref ""
let fstar_home = ref ""
let fstar_options = ref []
let krml_home = ref ""

let log fmt =
  let buf = Buffer.create 16 in
  Buffer.add_string buf Ansi.blue;
  Printf.kbprintf (fun buf ->
    Buffer.add_string buf Ansi.reset;
    Buffer.add_string buf "\n";
    Buffer.output_buffer stdout buf
  ) buf fmt

let detect_fstar () =
  (* All our paths use "/" as a separator, INCLUDING windows paths because
   * they're run through cygpath -m *)
  let (^^) x y = x ^ "/" ^ y  in

  let readlink =
    if Sys.command "which greadlink" = 0 then
      "greadlink"
    else
      "readlink"
  in
  log "readlink is: %s" readlink;

  let real_krml =
    try String.trim (Utils.run_and_read readlink [| "-f"; Sys.argv.(0) |])
    with _ -> fatal_error "Could not compute full krml path"
  in
  log "the Kremlin executable is: %s" real_krml;

  let output =
    try String.trim (Utils.run_and_read "dirname" [| real_krml |])
    with _ -> fatal_error "Could not compute krml home"
  in
  log "KreMLin home is: %s" output;
  krml_home := output;

  let output =
    try String.trim (Utils.run_and_read "which" [| "fstar.exe" |])
    with _ -> fatal_error "Could not locate fstar.exe"
  in
  log "fstar is: %s" output;
  fstar := output;

  let output =
    try String.trim (Utils.run_and_read readlink [| "-f"; !fstar ^^ ".." |])
    with _ -> fatal_error "Could not locate $FSTAR_HOME"
  in
  log "fstar home is: %s" output;
  fstar_home := output;

  let has_cygpath = Sys.command "which cygpath" = 0 in
  if has_cygpath then begin
    fstar := String.trim (Utils.run_and_read "cygpath" [| "-m"; !fstar |]);
    log "fstar converted to windows path: %s" !fstar;
    fstar_home := String.trim (Utils.run_and_read "cygpath" [| "-m"; !fstar_home |]);
    log "fstar home converted to windows path: %s" !fstar_home
  end;

  let fstar_includes = [
    !fstar_home ^^ "examples" ^^ "low-level";
    !fstar_home ^^ "examples" ^^ "low-level" ^^ "crypto";
    !krml_home ^^ "kremlib"
  ] in
  fstar_options := [
    "--lax"; "--trace_error"; "--codegen"; "Kremlin"
  ] @ List.flatten (List.map (fun d -> ["--include"; d]) fstar_includes);
  log "fstar is: %s %s" !fstar (String.concat " " !fstar_options)

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
  log "calling: %s %s" !fstar (String.concat " " args);
  match Utils.run !fstar (Array.of_list args) with
  | Unix.WEXITED 0, stdout ->
      log "fstar exited normally%s" (verbose_msg ());
      if !Options.verbose then
        print_string stdout;
      "out.krml"
  | _ ->
      fatal_error "fstar exited abnormally!"
