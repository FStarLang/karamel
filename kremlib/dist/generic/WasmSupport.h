/*
  Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
  Licensed under the Apache 2.0 License.
*/

#include <inttypes.h>
#include "kremlib.h"
#include "kremlin/internal/compat.h"
#include "kremlin/internal/target.h"

#ifndef __WasmSupport_H
#define __WasmSupport_H




extern void WasmSupport_trap();

uint32_t WasmSupport_align_64(uint32_t x);

void WasmSupport_check_buffer_size(uint32_t s);

uint32_t WasmSupport_betole32(uint32_t x);

uint64_t WasmSupport_betole64(uint64_t x);

#define __WasmSupport_H_DEFINED
#endif
