#ifndef __KREMSTR_H
#define __KREMSTR_H

#include "kremlib.h"

typedef const char *C_String_t, *C_String_t_;

static inline char char_of_uint8(uint8_t x) {
  return (char) x;
}

static inline const char *C_String_of_literal (const char *str) {
  return str;
}

static inline uint32_t bufstrcpy(char *dst, const char *src) {
  char *end = stpcpy(dst, src);
  return end - dst;
}

static inline uint32_t print_u32(char *dst, uint32_t i) {
  return sprintf(dst, "%"PRIu32, i);
}

Prims_string Prims_strcat(Prims_string s0, Prims_string s1);

#endif
