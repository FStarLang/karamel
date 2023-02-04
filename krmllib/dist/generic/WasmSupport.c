/*
  Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
  Licensed under the Apache 2.0 License.
*/


#include "WasmSupport.h"



uint32_t WasmSupport_align_64(uint32_t x)
{
  if (!((x & (uint32_t)0x07U) == (uint32_t)0U))
  {
    return (x & (uint32_t)4294967288U) + (uint32_t)0x08U;
  }
  else
  {
    return x;
  }
}

void WasmSupport_check_buffer_size(uint32_t s)
{
  if (s == (uint32_t)0U)
  {
    WasmSupport_trap("Zero-sized arrays are not supported in C and in WASM either. See WasmSupport.fst");
  }
}

uint32_t WasmSupport_betole32(uint32_t x)
{
  return
    (((x >> (uint32_t)24U & (uint32_t)0x000000FFU) | (x >> (uint32_t)8U & (uint32_t)0x0000FF00U))
    | (x << (uint32_t)8U & (uint32_t)0x00FF0000U))
    | (x << (uint32_t)24U & (uint32_t)0xFF000000U);
}

uint64_t WasmSupport_betole64(uint64_t x)
{
  uint64_t low = (uint64_t)WasmSupport_betole32((uint32_t)x);
  uint64_t high = (uint64_t)WasmSupport_betole32((uint32_t)(x >> (uint32_t)32U));
  return low << (uint32_t)32U | high;
}

void WasmSupport_memzero(uint8_t *x, uint32_t len, uint32_t sz)
{
  if (len >= (uint32_t)0xffffffffU / sz)
  {
    WasmSupport_trap("Overflow in memzero; see WasmSupport.fst");
  }
  uint32_t n_bytes = len * sz;
  for (uint32_t i = (uint32_t)0U; i < n_bytes; i++)
  {
    x[i] = (uint8_t)0U;
  }
}

