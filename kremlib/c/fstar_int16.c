#include "FStar_Int16.h"

Prims_string FStar_Int16_to_string(uint16_t i) {
  char *buf = KRML_HOST_MALLOC(24);
  snprintf(buf, 24, "%"PRId16, i);
  return buf;
}
