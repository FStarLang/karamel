(* Actually printing out Rust *)

open PPrint

(* It is understood that many of these need to go once the code-gen is improved. *)
let directives = ref (String.trim {|
#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unreachable_patterns)]
|})

let use_aligned = ref false

let rust_name f = f ^ ".rs"

let write_file file =
  let prefix, decls = file in
  if decls <> [] then
    (* TODO: directory structure according to the prefix *)
    let dirs, filename = KList.split_at_last prefix in
    let base = if !Options.tmpdir <> "" then !Options.tmpdir else "." in
    let dirs = List.fold_left Driver.((^^)) base dirs in
    Driver.mkdirp dirs;
    let filename = Driver.((^^)) dirs (rust_name filename) in
    Utils.with_open_out_bin filename (fun oc ->
      let doc =
        string !directives ^^ hardline ^^ hardline ^^
        (if !use_aligned then string "use aligned::*;" ^^ hardline ^^ hardline else empty) ^^
        PrintMiniRust.print_decls prefix decls
      in
      PPrint.ToChannel.pretty 0.95 100 oc doc
    );
    Some filename
  else
    None

let write_all files =
  Driver.maybe_create_output_dir ();
  let filenames = List.map write_file files in
  let filenames = KList.filter_some filenames in
  if Options.debug "rs-filenames" then
    KPrint.bfprintf stdout "INFO: wrote %d files\n%s\n" (List.length filenames)
      (String.concat "\n" filenames);
  if !PrintMiniRust.failures > 0 then
    KPrint.bprintf "%s%d total printing errors%s\n" Ansi.red !PrintMiniRust.failures Ansi.reset
