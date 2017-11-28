#ifndef __KREMSTR_H
#define __KREMSTR_H

#include "kremlib.h"

/******************************************************************************/
/* Implementation of C.String                                                 */
/******************************************************************************/

/* Note: we drop C.String, which means that generated programs do not see
 * "extern" declarations, meaning that we can implement these functions via a
 * header only. */

typedef const char *C_String_t, *C_String_t_;

static inline char char_of_uint8(uint8_t x) {
  return (char) x;
}

static inline const char *C_String_of_literal (const char *str) {
  return str;
}

static inline uint32_t bufstrcpy(char *dst, const char *src) {
  /* The F* precondition guarantees that src is zero-terminated */
  return sprintf(dst, "%s", src);
}

static inline uint32_t print_u32(char *dst, uint32_t i) {
  return sprintf(dst, "%"PRIu32, i);
}

static inline void C_String_print(C_String_t str) {
  printf("%s", str);
}

/******************************************************************************/
/* Prims stubs                                                                */
/******************************************************************************/

typedef const char *Prims_string;
Prims_string Prims_strcat(Prims_string s0, Prims_string s1);

static inline Prims_string FStar_Int64_to_string(uint64_t i) {
  char *buf = malloc(24);
  snprintf(buf, 24, "%"PRId64, i);
  return buf;
}

static inline Prims_string FStar_Int32_to_string(uint32_t i) {
  char *buf = malloc(24);
  snprintf(buf, 24, "%"PRId32, i);
  return buf;
}

static inline Prims_string FStar_Int16_to_string(uint16_t i) {
  char *buf = malloc(24);
  snprintf(buf, 24, "%"PRId16, i);
  return buf;
}

static inline Prims_string FStar_Int8_to_string(uint8_t i) {
  char *buf = malloc(24);
  snprintf(buf, 24, "%"PRId8, i);
  return buf;
}

static inline Prims_string FStar_UInt64_to_string(uint64_t i) {
  char *buf = malloc(24);
  snprintf(buf, 24, "%"PRIu64, i);
  return buf;
}

static inline Prims_string FStar_UInt32_to_string(uint32_t i) {
  char *buf = malloc(24);
  snprintf(buf, 24, "%"PRIu32, i);
  return buf;
}

static inline Prims_string FStar_UInt16_to_string(uint16_t i) {
  char *buf = malloc(24);
  snprintf(buf, 24, "%"PRIu16, i);
  return buf;
}

static inline Prims_string FStar_UInt8_to_string(uint8_t i) {
  char *buf = malloc(24);
  snprintf(buf, 24, "%"PRIu8, i);
  return buf;
}

static inline Prims_string Prims_string_of_int(krml_checked_int_t i) {
  return FStar_Int32_to_string(i);
}

static inline Prims_string Prims_string_of_bool(bool b) {
  if (b) {
    return "true";
  } else {
    return "false";
  }
}
#endif
