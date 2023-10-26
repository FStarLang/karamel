/*
  Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
  Licensed under the Apache 2.0 License.
*/


#include "WasmSupport.h"

uint32_t WasmSupport_align_64(uint32_t x)
{
  if (!((x & 0x07U) == 0U))
  {
    return (x & 4294967288U) + 0x08U;
  }
  else
  {
    return x;
  }
}

void WasmSupport_check_buffer_size(uint32_t s)
{
  if (s == 0U)
  {
    WasmSupport_trap("Zero-sized arrays are not supported in C and in WASM either. See WasmSupport.fst");
  }
}

uint16_t WasmSupport_betole16(uint16_t x)
{
  return ((uint32_t)x >> 8U & 0x00FFU) | ((uint32_t)x << 8U & 0xFF00U);
}

uint32_t WasmSupport_betole32(uint32_t x)
{
  return
    (((x >> 24U & 0x000000FFU) | (x >> 8U & 0x0000FF00U)) | (x << 8U & 0x00FF0000U))
    | (x << 24U & 0xFF000000U);
}

uint64_t WasmSupport_betole64(uint64_t x)
{
  uint64_t low = (uint64_t)WasmSupport_betole32((uint32_t)x);
  uint64_t high = (uint64_t)WasmSupport_betole32((uint32_t)(x >> 32U));
  return low << 32U | high;
}

void WasmSupport_memzero(uint8_t *x, uint32_t len, uint32_t sz)
{
  if (len >= 0xffffffffU / sz)
  {
    WasmSupport_trap("Overflow in memzero; see WasmSupport.fst");
  }
  uint32_t n_bytes = len * sz;
  for (uint32_t i = 0U; i < n_bytes; i++)
  {
    x[i] = 0U;
  }
}

