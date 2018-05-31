#include "FStar_IO.h"

bool FStar_IO_debug_print_string(Prims_string s) {
  KRML_HOST_PRINTF("%s", s);
  return false;
}
