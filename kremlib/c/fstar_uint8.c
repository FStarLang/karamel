#include "FStar_UInt8.h"

uint8_t FStar_UInt8_eq_mask(uint8_t x, uint8_t y) {
  x = ~(x ^ y);
  x &= x << 4;
  x &= x << 2;
  x &= x << 1;
  return (int8_t)x >> 7;
}

uint8_t FStar_UInt8_gte_mask(uint8_t x, uint8_t y) {
  return ~(uint8_t)(((int32_t)x - y) >> 31);
}

Prims_string FStar_UInt8_to_string(uint8_t i) {
  char *buf = KRML_HOST_MALLOC(24);
  KRML_HOST_SNPRINTF(buf, 24, "%"PRIu8, i);
  return buf;
}

uint8_t FStar_UInt8_uint_to_t(krml_checked_int_t x) {
  /* TODO bounds check */
  return x;
}

krml_checked_int_t FStar_UInt8_v(uint8_t x) {
  return x;
}
