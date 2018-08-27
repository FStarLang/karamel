#include "FStar_UInt32.h"

Prims_string FStar_UInt32_to_string(uint32_t i) {
  char *buf = KRML_HOST_MALLOC(24);
  KRML_HOST_SNPRINTF(buf, 24, "%"PRIu32, i);
  return buf;
}

uint32_t FStar_UInt32_uint_to_t(krml_checked_int_t x) {
  /* TODO bounds check */
  return x;
}

krml_checked_int_t FStar_UInt32_v(uint32_t x) {
  RETURN_OR(x);
}
