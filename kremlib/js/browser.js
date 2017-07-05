// This module expects that all custom JS files have already been brought into
// scope, that my_modules contains a list of .wasm files, and that it is
// included from a webpage.
var my_print = console.log;

my_print("... assembling WASM modules " + my_modules);
Promise.all(my_modules.map(m => fetch(m + ".wasm")))
  .then(responses =>
    Promise.all(responses.map(r => r.arrayBuffer()))
  ).then(bufs =>
    link(bufs.map((b, i) => ({ buf: b, name: my_modules[i] }))))
  .then(scope => {
    var found = false;
    for (let m of Object.keys(scope)) {
      if ("main" in scope[m]) {
        my_print("... main found in module " + m);
        m.main();
        break;
      }
    }
    if (!found) {
      if (!("main" in window)) {
        my_print("... no main in current window");
        throw "Aborting";
      }
      main();
    }
  }).catch(e =>
    my_print(e)
  );
