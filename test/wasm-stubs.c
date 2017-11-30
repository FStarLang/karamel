#include <stdlib.h>

// Just so that we can try out the Wasm-specific transformations performed on
// Ast while still compiling to C.
void WasmSupport_trap() {
  exit(1);
}
