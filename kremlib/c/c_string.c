#include "C_String.h"

C_String_t C_String_of_literal (const char *str) {
  return str;
}

void C_String_print(C_String_t str) {
  KRML_HOST_PRINTF("%s", str);
}
