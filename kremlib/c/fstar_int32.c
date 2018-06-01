#include "FStar_Int32.h"

Prims_string FStar_Int32_to_string(int32_t i) {
  char *buf = KRML_HOST_MALLOC(24);
  snprintf(buf, 24, "%"PRId32, i);
  return buf;
}

krml_checked_int_t FStar_Int32_v(int32_t x) {
  return x;
}
