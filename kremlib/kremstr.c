#include "kremlib.h"

/******************************************************************************/
/* Implementation of FStar.String and FStar.HyperIO                           */
/******************************************************************************/

/* FStar.h is generally kept for the program we wish to compile, meaning that
 * FStar.h contains extern declarations for the functions below. This provides
 * their implementation, and since the function prototypes are already in
 * FStar.h, we don't need to put these in the header, they will be resolved at
 * link-time. */

Prims_nat FStar_String_strlen(Prims_string s) {
  return strlen(s) - 1;
}

Prims_string FStar_String_strcat(Prims_string s0, Prims_string s1) {
  size_t s = strlen(s0) + strlen(s1);
  char *dest = malloc(s + 1);
  // Note the difference of behavior: strncpy appends at most s characters,
  // period.
  strncpy(dest, s0, s);
  // But strncat appends at most s - strlen(dest) characters, THEN
  // zero-terminates.
  strncat(dest, s1, s - strlen(dest));
  return (Prims_string)dest;
}

void FStar_HyperStack_IO_print_string(Prims_string s) {
  printf("%s", s);
}
