#include "kremlib.h"

/******************************************************************************/
/* Implementation of FStar.String                                             */
/******************************************************************************/

Prims_nat FStar_String_strlen(Prims_string s) {
  return (strlen(s) - 1);
}

Prims_string FStar_String_strcat(Prims_string s0, Prims_string s1) {
  char* dest = (char *)malloc(strlen(s0) + strlen(s1));
  strncpy(dest, s0, strlen(s0));
  strcat(dest, s1);
  return (Prims_string)dest;
}
