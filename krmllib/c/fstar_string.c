/* Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
   Licensed under the Apache 2.0 and MIT Licenses. */

#include "Prims.h"
#include "FStar_String.h"


/* F* now imposes utf8 encoding for string literals.
 *
 * We assume only well-formed utf8 string literals, e.g. no overlong invalid
 * encodings, etc. */
Prims_nat FStar_String_strlen(Prims_string s) {
  uint64_t count = 0;
  uint64_t i = 0;
  while (s[i]) {
    uint8_t byte = (uint8_t) s[i];
    if ((byte & 0xc0) != 0x80)
      // Not a continuation byte, i.e. start of a codepoint.
      count++;
    i++;
  }
  return count;
}

/* Backwards-compatibility; remove me. */
Prims_string FStar_String_strcat(Prims_string s0, Prims_string s1) {
  return Prims_strcat(s0, s1);
}


krml_checked_int_t FStar_String_index_of(Prims_string s1, FStar_Char_char fc) {
  if (fc > 127) {
    KRML_HOST_PRINTF("FStar.Char.char overflow at %s:%d\n", __FILE__, __LINE__);
    KRML_HOST_EXIT(252);
  }
  char c = fc;
  char *pos = strchr(s1, c);
  return (pos ? pos - s1 : -1);
}

Prims_string FStar_String_substring(
    Prims_string s0, krml_checked_int_t from, krml_checked_int_t length) {
  char *dest = KRML_HOST_CALLOC(length + 1, 1); // zero terminated
#ifdef _MSC_VER
  strncpy_s(dest, length + 1, s0 + from, length);
#else
  strncpy(dest, s0 + from, length);
#endif
  return dest;
}

