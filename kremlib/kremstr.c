#include "kremlib.h"
#include "kremstr.h"

/******************************************************************************/
/* Implementation of FStar.String and FStar.HyperIO                           */
/******************************************************************************/

/* FStar.h is generally kept for the program we wish to compile, meaning that
 * FStar.h contains extern declarations for the functions below. This provides
 * their implementation, and since the function prototypes are already in
 * FStar.h, we don't need to put these in the header, they will be resolved at
 * link-time. */

Prims_nat FStar_String_strlen(Prims_string s) {
  return strlen(s);
}

Prims_string FStar_String_strcat(Prims_string s0, Prims_string s1) {
  char *dest = calloc(strlen(s0) + strlen(s1) + 1, 1);
  strcat(dest, s0);
  strcat(dest, s1);
  return (Prims_string)dest;
}

Prims_string Prims_strcat(Prims_string s0, Prims_string s1) {
  return FStar_String_strcat(s0, s1);
}

void FStar_HyperStack_IO_print_string(Prims_string s) {
  printf("%s", s);
}

void FStar_IO_debug_print_string(Prims_string s) {
  printf("%s", s);
}

bool __eq__Prims_string(Prims_string s1, Prims_string s2) {
  return (strcmp(s1, s2) == 0);
}

krml_checked_int_t FStar_String_index_of(Prims_string s1, FStar_Char_char fc) {
  if (fc > UINT8_MAX) {
      KRML_HOST_PRINTF(                                                        \
          "FStar.Char.char overflow at %s:%d\n", __FILE__,         \
          __LINE__);                                                           \
      KRML_HOST_EXIT(252);                                                     \
  }
  char c = fc;
  char *pos = strchr (s1, c);
  return (pos ? pos - s1 : -1);
}

Prims_string FStar_String_substring(Prims_string s0, krml_checked_int_t from, krml_checked_int_t length) {
  char *dest = calloc(length + 1, 1); //zero terminated
  strncpy(dest, s0 + from, length);
  return (Prims_string)dest;
}

