(* Copyright (c) INRIA and Microsoft Corporation. All rights reserved. *)
(* Licensed under the Apache 2.0 License. *)

(* Output a set of Wasm files, along with toplevel entry files (HTML for a
 * browser, .js for a shell). *)

let html_stub = format_of_string {|
<!doctype html>
<html>
  <head>
    <meta charset="utf-8">
    <title>KreMLin main driver</title>
    %s
    <script type="application/javascript">
      var my_modules = %s;
    </script>
    <script type="application/javascript" src="browser.js"></script>
    <script type="application/javascript" src="loader.js"></script>
    <script type="application/javascript">
      window.addEventListener("load", kremlin_start);
    </script>
  </head>
  <body>
    <pre id="terminal"></pre>
  </body>
</html>
|}

let script_stub = format_of_string {|
    <script type="application/javascript" src="%s"></script>
|}

let shell_stub = format_of_string {|
// To be loaded by main.js
var my_js_files = %s;
var my_modules = %s;
var my_debug = %b;

if (typeof module !== "undefined")
  module.exports = {
    my_js_files: my_js_files,
    my_modules: my_modules,
    my_debug: my_debug
  }
|}

let as_js_list l =
  "[" ^ String.concat ", " (List.map (fun s ->
    "\"" ^ s ^ "\""
  ) l) ^ "]"

let readme =
{|How to run the WASM output of KreMLin?

# With v8, from the console

Install and build Google's v8 engine, which should give a d8 binary. Then:

    d8 --allow-natives-syntax main.js

Note: on my machine, it's better to call d8 through an absolute path.

# With Chakra, from the console

Install and build ChakraCore, which should give a ch binary. Then:

    ch -Wasm main.js

# With Chrome, from the browser

Chrome won't run this from the file:// URL, so you'll need to start an HTTP
server from this directory. If you don't have one already:

    npm install http-server

Then, run `http-server .` and navigate to http://localhost:8080/main.html
|}

let write_all js_files modules print =
  Driver.detect_kremlin_if ();
  Driver.mkdirp !Options.tmpdir;

  (* Write out all the individual .wasm files *)
  List.iter (fun (name, module_) ->
    (* Write a .wast for debugging purposes. *)
    let script = [ CFlatToWasm.dummy_phrase (Wasm.Script.Module (
      None,
      CFlatToWasm.dummy_phrase (Wasm.Script.Textual module_)))]
    in
    Utils.with_open_out_bin (Filename.concat !Options.tmpdir (name ^ ".wast")) (fun oc ->
      Wasm.Print.script oc 80 `Textual script);
    (* Now the actual .wasm *)
    let s = Wasm.Encode.encode module_ in
    let name = name ^ ".wasm" in
    Utils.with_open_out_bin (Filename.concat !Options.tmpdir name) (fun oc -> output_string oc s);
    KPrint.bprintf "Wrote %s\n" name;
    if print then
      Wasm.Print.module_ stdout Utils.twidth module_;
    flush stderr
  ) modules;

  (* Write out HTML file *)
  let html_file = Filename.concat !Options.tmpdir "main.html" in
  let module_list = as_js_list (List.map fst modules) in
  Utils.with_open_out_bin html_file (fun oc ->
    let pre_load = String.concat "" (List.map (fun f ->
      Printf.sprintf script_stub f
    ) js_files) in
    Printf.fprintf oc html_stub pre_load module_list
  );

  (* A stub for shell usage *)
  let shell_file = Filename.concat !Options.tmpdir "shell.js" in
  let js_file_list = as_js_list js_files in
  Utils.with_open_out_bin shell_file (fun oc ->
    Printf.fprintf oc shell_stub js_file_list module_list (Options.debug "wasm-memory")
  );

  (* Files that are needed for the tmpdir to be runnable and complete. *)
  let ( ^^ ) = Filename.concat in
  List.iter (fun f ->
    Utils.cp (!Options.tmpdir ^^ f) (!Driver.kremlib_dir ^^ "js" ^^ f)
  ) [ "browser.js"; "loader.js"; "main.js" ];

  (* Be nice *)
  Utils.with_open_out_bin (!Options.tmpdir ^^ "README") (fun oc -> output_string oc readme)
