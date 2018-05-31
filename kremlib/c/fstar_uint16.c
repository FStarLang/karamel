#include "FStar_UInt16.h"

uint16_t FStar_UInt16_eq_mask(uint16_t x, uint16_t y) {
  x = ~(x ^ y);
  x &= x << 8;
  x &= x << 4;
  x &= x << 2;
  x &= x << 1;
  return (int16_t)x >> 15;
}

uint16_t FStar_UInt16_gte_mask(uint16_t x, uint16_t y) {
  return ~(uint16_t)(((int32_t)x - y) >> 31);
}

Prims_string FStar_UInt16_to_string(uint16_t i) {
  char *buf = KRML_HOST_MALLOC(24);
  snprintf(buf, 24, "%"PRIu16, i);
  return buf;
}

uint16_t FStar_UInt16_uint_to_t(krml_checked_int_t x) {
  /* TODO bounds check */
  return x;
}

krml_checked_int_t FStar_UInt16_v(uint16_t x) {
  return x;
}
