// This module expect a file named shell.js, that defines my_js_files and
// my_modules to be arrays of filenames.
// The former are loaded into scope, and the latter are folded with name
// propagation just like kreMLin WASM codegen expects.
// Once everything is loaded, we try to find a main function in any of the
// modules, or call the main function in scope, or fail.
"use strict";

var debug = true;

var my_load;

if ("load" in this)
  my_load = load;
else if ("WScript" in this)
  my_load = WScript.LoadScriptFile;
else
  throw "Unsupported shell: try running [d8 <this-file>] or [ch -Wasm <this-file>]";

if (!("WebAssembly" in this))
  throw "WebAssembly not enabled; are you running an old shell, or missing [-Wasm]?";

var my_print = print;

my_print("... loader.js");
my_load("loader.js");
// Written out by KreMLin so as to fill in my_js_files and my_modules.
my_load("shell.js");

my_print("... custom JS modules " + my_js_files);
for (let f of my_js_files)
  my_load(f);

my_print("... assembling WASM modules " + my_modules + "\n");
var scope = link(my_modules.map(m => ({ name: m, buf: readbuffer(m+".wasm") })));
scope.then(scope => {
  if (debug) {
    for (let m of Object.keys(scope))
      my_print("... " + m + " exports " + Object.keys(scope[m]).join(","));
  }

  var found = false;
  for (let m of Object.keys(scope)) {
    if ("main" in scope[m]) {
      my_print("... main found in module " + m);
      m.main();
      break;
    }
  }
  if (!found) {
    if (!("main" in this)) {
      my_print("... no main in current scope");
      throw "Aborting";
    }
    main(scope);
  }
}).catch(e =>
  my_print(e)
);
