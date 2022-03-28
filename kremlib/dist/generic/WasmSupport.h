/*
  Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
  Licensed under the Apache 2.0 License.
*/


#ifndef __WasmSupport_H
#define __WasmSupport_H




#include <inttypes.h>
#include "kremlib.h"
#include "kremlin/internal/compat.h"
#include "kremlin/internal/target.h"
extern void WasmSupport_trap(Prims_string uu___);

extern uint32_t WasmSupport_malloc(uint32_t uu___);

uint32_t WasmSupport_align_64(uint32_t x);

void WasmSupport_check_buffer_size(uint32_t s);

uint32_t WasmSupport_betole32(uint32_t x);

uint64_t WasmSupport_betole64(uint64_t x);

void WasmSupport_memzero(uint8_t *x, uint32_t len, uint32_t sz);


#define __WasmSupport_H_DEFINED
#endif
