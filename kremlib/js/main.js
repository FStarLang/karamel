// This module expect a file named shell.js, that defines my_js_files and
// my_modules to be arrays of filenames.
// The former are loaded into scope, and the latter are folded with name
// propagation just like kreMLin WASM codegen expects.
// Once everything is loaded, we try to find a main function in any of the
// modules, or call the main function in scope, or fail.
"use strict";

var debug = true;

var my_load;
var my_print;
var my_quit;

if ("load" in this) {
  my_load = load;
  my_print = print;
  my_quit = quit;
} else if ("WScript" in this) {
  // Keys in WScript: Echo, Quit, LoadScriptFile, LoadScript, LoadModule,
  // SetTimeout, ClearTimeout, Attach, Detach, DumpFunctionPosition,
  // RequestAsyncBreak, LoadBinaryFile, LoadTextFile, Flag, Edit, Platform,
  // Arguments
  my_load = WScript.LoadScriptFile;
  my_print = WScript.Echo;
  my_quit = WScript.Quit;
} else
  throw "Unsupported shell: try running [d8 <this-file>] or [ch -Wasm <this-file>]";

if (!("WebAssembly" in this))
  throw "WebAssembly not enabled; are you running an old shell, or missing [-Wasm]?";

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

  let found = false;
  let err = 0;
  let with_debug = (main) => {
    if (my_debug)
      dump(scope.Kremlin.mem, 2048);
    err = main(scope);
    if (my_debug)
      dump(scope.Kremlin.mem, 2048);
  };
  for (let m of Object.keys(scope)) {
    if ("main" in scope[m]) {
      my_print("... main found in module " + m);
      found = true;
      with_debug(scope[m].main);
    }
  }
  if (!found) {
    if (!("main" in this)) {
      my_print("... no main in current scope");
      throw new Error("Aborting");
    }
    with_debug(main);
  }
  my_print("... done running main");
  my_quit(err);
}).catch(e => {
  my_print("... error running main");
  my_print(e.stack);
  my_quit(255);
});

Promise.resolve(scope);
