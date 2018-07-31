#include "FStar_UInt64.h"

uint64_t FStar_UInt64_eq_mask(uint64_t x, uint64_t y) {
  x = ~(x ^ y);
  x &= x << 32;
  x &= x << 16;
  x &= x << 8;
  x &= x << 4;
  x &= x << 2;
  x &= x << 1;
  return ((int64_t)x) >> 63;
}

uint64_t FStar_UInt64_gte_mask(uint64_t x, uint64_t y) {
  uint64_t low63 = ~((uint64_t)(
      (int64_t)(
          (int64_t)(x & UINT64_C(0x7fffffffffffffff)) -
          (int64_t)(y & UINT64_C(0x7fffffffffffffff))) >>
      63));
  uint64_t high_bit = ~((uint64_t)(
      (int64_t)(
          (int64_t)(x & UINT64_C(0x8000000000000000)) -
          (int64_t)(y & UINT64_C(0x8000000000000000))) >>
      63));
  return low63 & high_bit;
}

Prims_string FStar_UInt64_to_string(uint64_t i) {
  char *buf = KRML_HOST_MALLOC(24);
  KRML_HOST_SNPRINTF(buf, 24, "%"PRIu64, i);
  return buf;
}

uint64_t FStar_UInt64_uint_to_t(krml_checked_int_t x) {
  /* TODO bounds check */
  return x;
}

krml_checked_int_t FStar_UInt64_v(uint64_t x) {
  RETURN_OR(x);
}
