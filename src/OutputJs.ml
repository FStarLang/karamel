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
  </head>
  <body>
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
|}

let as_js_list l =
  "[" ^ String.concat ", " (List.map (fun s ->
    "\"" ^ s ^ "\""
  ) l) ^ "]"

let write_all js_files modules print =
  (* Write out all the individual .wasm files *)
  List.iter (fun (name, module_) ->
    let s = Wasm.Encode.encode module_ in
    let name = name ^ ".wasm" in
    Utils.with_open_out (Filename.concat !Options.tmpdir name) (fun oc -> output_string oc s);
    KPrint.bprintf "Wrote %s\n" name;
    if print then
      Wasm.Print.module_ stdout Utils.twidth module_;
    flush stderr
  ) modules;

  (* Write out HTML file *)
  let html_file = Filename.concat !Options.tmpdir "main.html" in
  let module_list = as_js_list (List.map fst modules) in
  Utils.with_open_out html_file (fun oc ->
    let pre_load = String.concat "" (List.map (fun f ->
      Printf.sprintf script_stub f
    ) js_files) in
    Printf.fprintf oc html_stub pre_load module_list
  );

  (* A stub for shell usage *)
  let shell_file = Filename.concat !Options.tmpdir "shell.js" in
  let js_file_list = as_js_list js_files in
  Utils.with_open_out shell_file (fun oc ->
    Printf.fprintf oc shell_stub js_file_list module_list
  )
