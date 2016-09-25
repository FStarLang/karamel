#include <stdlib.h>
#include "kremlib.h"

int exit_success = 0;

uint64_t FStar_UInt64_gte_mask(uint64_t x, uint64_t y) {
  return x >= y ? UINT64_C(0xffffffffffffffff) : 0;
}

uint64_t FStar_UInt64_eq_mask(uint64_t x, uint64_t y) {
  return x == y ? UINT64_C(0xffffffffffffffff) : 0;
}

Prims_int FStar_UInt32_v(uint32_t x) {
  exit(254);
}

FStar_Seq_seq FStar_Seq_createEmpty(void *_) {
  exit(254);
}
