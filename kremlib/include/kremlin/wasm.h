#ifndef __KREMLIN_WASM_H
#define __KREMLIN_WASM_H

/* This file is automatically included when compiling with -wasm -d force-c */
#define WasmSupport_check_buffer_size(X)

/* For tests only: we might need this function to be forward-declared, because
 * the dependency on WasmSupport appears very late, after SimplifyWasm, and
 * sadly, after the topological order has been done. */
void WasmSupport_check_buffer_size(uint32_t s);

#endif
