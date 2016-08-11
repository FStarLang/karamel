#include <stdlib.h>
#include "kremlib.h"

uint64_t FStar_UInt64_gte_mask(uint64_t x, uint64_t y) {
  return x >= y ? UINT64_C(0xffffffffffffffff) : 0;
}

uint64_t FStar_UInt64_eq_mask(uint64_t x, uint64_t y) {
  return x == y ? UINT64_C(0xffffffffffffffff) : 0;
}

Prims_int FStar_UInt32_v(uint32_t x) {
  exit(254);
}

int C_exit_success = 0;
