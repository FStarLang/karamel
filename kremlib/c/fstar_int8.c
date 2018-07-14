#include "FStar_Int8.h"

Prims_string FStar_Int8_to_string(int8_t i) {
  char *buf = KRML_HOST_MALLOC(24);
  snprintf(buf, 24, "%"PRId8, i);
  return buf;
}
