/* Garbage-collected fat pointers that keep track of their lengths. */
#ifndef __KREMBYTES_H
#ifndef __FStar_H
#define __KREMBYTES_H

#include <inttypes.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "FStar.h"
#include "Prims.h"

typedef uint8_t FStar_Bytes_byte;

#define CHECK(x)                                                               \
  do {                                                                         \
    if (!(x)) {                                                                \
      fprintf(stderr, "malloc failed at %s:%d", __FILE__, __LINE__);           \
      exit(253);                                                               \
    }                                                                          \
  } while (0)

static inline FStar_Bytes_bytes FStar_Bytes_copy(FStar_Bytes_bytes b1) {
  return b1;
}

static inline krml_checked_int_t FStar_Bytes_length(FStar_Bytes_bytes b) {
  return b.length;
}

static FStar_Bytes_bytes FStar_Bytes_empty_bytes = { .length = 0,
                                                     .data = NULL };

static inline FStar_Bytes_byte
FStar_Bytes_get(FStar_Bytes_bytes b, uint32_t i) {
  return (FStar_Bytes_byte)b.data[i];
}

static inline FStar_Bytes_bytes
FStar_Bytes_set_byte(FStar_Bytes_bytes b1, uint32_t i, FStar_Bytes_byte v) {
  char *data = malloc(b1.length);
  CHECK(data);
  memcpy(data, b1.data, b1.length);
  data[i] = v;
  FStar_Bytes_bytes b2 = { .length = b1.length, .data = data };
  return b2;
}

static inline FStar_Bytes_bytes
FStar_Bytes_create(uint32_t length, FStar_Bytes_byte initial) {
  char *data = malloc(length);
  CHECK(data);
  memset(data, initial, length);
  FStar_Bytes_bytes b = { .length = length, .data = data };
  return b;
}

static inline FStar_Bytes_bytes
FStar_Bytes_init(uint32_t length, FStar_Bytes_byte (*initial)(uint32_t i)) {
  char *data = malloc(length);
  CHECK(data);
  for (uint32_t i = 0; i < length; ++i)
    data[i] = initial(i);
  FStar_Bytes_bytes b = { .length = length, .data = data };
  return b;
}

static inline FStar_Bytes_bytes FStar_Bytes_abyte(FStar_Bytes_byte v1) {
  char *data = malloc(1);
  CHECK(data);
  data[0] = v1;
  FStar_Bytes_bytes b = { .length = 1, .data = data };
  return b;
}

static inline FStar_Bytes_bytes FStar_Bytes_twobytes(K___uint8_t_uint8_t v) {
  char *data = malloc(2);
  CHECK(data);
  data[0] = v.fst;
  data[1] = v.snd;
  FStar_Bytes_bytes b = { .length = 2, .data = data };
  return b;
}

static inline FStar_Bytes_bytes
FStar_Bytes_append(FStar_Bytes_bytes b1, FStar_Bytes_bytes b2) {
  // Overflow check
  uint32_t length = Prims_op_Addition(b1.length, b2.length);
  char *data = malloc(length);
  CHECK(data);
  if (b1.length > 0)
    memcpy(data, b1.data, b1.length);
  if (b2.length > 0)
    memcpy(data + b1.length, b2.data, b2.length);
  FStar_Bytes_bytes b = { .length = length, .data = data };
  return b;
}

static inline FStar_Bytes_bytes
FStar_Bytes_slice(FStar_Bytes_bytes b1, uint32_t s, uint32_t e) {
  if (s == e)
    return FStar_Bytes_empty_bytes;
  if (s > e) {
    fprintf(stderr, "!! s > e in FStar_Bytes_slice\n");
    exit(254);
  }

  uint32_t length = e - s;
  char *data = malloc(length);
  CHECK(data);
  memcpy(data, b1.data + s, length);
  FStar_Bytes_bytes b = { .length = length, .data = data };
  return b;
}

static inline FStar_Bytes_bytes
FStar_Bytes_sub(FStar_Bytes_bytes b1, uint32_t s, uint32_t l) {
  return FStar_Bytes_slice(b1, s, Prims_op_Addition(s, l));
}

static inline FStar_Bytes_bytes FStar_Bytes_utf8_encode(const char *str) {
  // Note: the original signature wants a Prims.string, which is GC-backed,
  // heap-allocated and immutable. So, it's fine to skip the copy (famous last
  // words?).
  // F* ought to guarantee at some point that i) strings are utf8-encoded and
  // ii) zero-terminated, so we can just see utf8 as bytes by using strlen which
  // is utf8-UNaware.
  FStar_Bytes_bytes b = { .length = strlen(str), .data = str };
  return b;
}

// DEPRECATED
static inline FStar_Bytes_bytes FStar_Bytes_bytes_of_string(const char *str) {
  return FStar_Bytes_utf8_encode(str);
}

static inline K___FStar_Bytes_bytes_FStar_Bytes_bytes
FStar_Bytes_split(FStar_Bytes_bytes bs, FStar_UInt32_t i) {
  K___FStar_Bytes_bytes_FStar_Bytes_bytes p = {
    .fst = FStar_Bytes_slice(bs, 0, i),
    .snd = FStar_Bytes_slice(bs, i, bs.length)
  };
  return p;
}

static inline FStar_UInt32_t FStar_Bytes_len(FStar_Bytes_bytes b1) {
  return b1.length;
}

// Right-shifts for negative values at a signed type are undefined behavior in
// C. However, the precondition of the function guarantees that `n` is a `nat`,
// meaning that if it overflew we'd catch it.
static inline FStar_Bytes_bytes
FStar_Bytes_bytes_of_int(krml_checked_int_t k, krml_checked_int_t n) {
  FStar_Bytes_bytes b = FStar_Bytes_create(k, 0);
  char *data = (char *)b.data;
  for (krml_checked_int_t i = k - 1; i >= 0; i--) {
    uint32_t offset = 8 * ((k - 1) - i);
    data[i] = (n >> offset) & 0xFF;
  }
  return b;
}

// TODO: #ifdef KRML_NOUINT128
static inline uint128_t
FStar_Bytes_uint128_of_bytes(FStar_Bytes_bytes bs) {
  uint128_t res = 0;
  for (uint32_t i = 0; i < bs.length; i++) {
    res = res << 8;
    res |= bs.data[i] & 0xFF;
  }
  return res;
}

static inline krml_checked_int_t
FStar_Bytes_int_of_bytes(FStar_Bytes_bytes bs) {
  if (bs.length > 4) {
    fprintf(stderr, "int_of_bytes overflow\n");
    exit(255);
  }
  krml_checked_int_t res = 0;
  for (uint32_t i = 0; i < bs.length; i++) {
    res = res << 8;
    // Note: this is a char, whose signedness is unspecified, so it may get an
    // evil sign-extension -- mask.
    res |= bs.data[i] & 0xFF;
  }
  return res;
}


static inline krml_checked_int_t FStar_Bytes_repr_bytes(Prims_nat bs) {
  if (bs < 0x100)
    return 1;
  else if (bs < 0x10000)
    return 2;
  else if (bs < 0x1000000)
    return 3;
  else
    return 4;
}

static inline FStar_Bytes_bytes
FStar_Bytes_xor(FStar_UInt32_t x, FStar_Bytes_bytes b1, FStar_Bytes_bytes b2) {
  char *data = malloc(x);
  CHECK(data);
  for (size_t i = 0; i < x; ++i)
    data[i] = b1.data[i] ^ b2.data[i];
  FStar_Bytes_bytes b = { .length = x, .data = data };
  return b;
}

static inline FStar_Bytes_bytes FStar_Bytes_bytes_of_hex(Prims_string str) {
  size_t l = strlen(str);
  if (l % 2 == 1)
    fprintf(
        stderr,
        "bytes_of_hex: input string has non-even length, truncating!\n");
  char *data = malloc(l / 2);
  CHECK(data);
  for (size_t i = 0; i < l / 2; i++) {
    uint8_t dst;
    int ret = sscanf(str + 2 * i, "%02" SCNx8, &dst);
    if (ret != 1) {
      fprintf(
          stderr,
          "bytes_of_hex: run-time error while scanning at index "
          "%zu\nret=%d\n%s\n",
          2 * i, ret, str);
      return FStar_Bytes_empty_bytes;
    }
    data[i] = dst;
  }
  FStar_Bytes_bytes b = { .length = l / 2, .data = data };
  return b;
}

static inline Prims_string FStar_Bytes_print_bytes(FStar_Bytes_bytes s) {
  char *str = malloc(s.length * 2 + 1);
  CHECK(str);
  for (size_t i = 0; i < s.length; ++i)
    sprintf(str + 2 * i, "%02" PRIx8, s.data[i] & 0xFF);
  str[s.length * 2] = 0;
  return str;
}

static inline Prims_string FStar_Bytes_hex_of_bytes(FStar_Bytes_bytes s) {
  return FStar_Bytes_print_bytes(s);
}

// https://www.cl.cam.ac.uk/~mgk25/ucs/utf8_check.c
static inline const unsigned char *utf8_check(const unsigned char *s) {
  while (*s) {
    if (*s < 0x80)
      /* 0xxxxxxx */
      s++;
    else if ((s[0] & 0xe0) == 0xc0) {
      /* 110XXXXx 10xxxxxx */
      if ((s[1] & 0xc0) != 0x80 || (s[0] & 0xfe) == 0xc0) /* overlong? */
        return s;
      else
        s += 2;
    } else if ((s[0] & 0xf0) == 0xe0) {
      /* 1110XXXX 10Xxxxxx 10xxxxxx */
      if ((s[1] & 0xc0) != 0x80 || (s[2] & 0xc0) != 0x80 ||
          (s[0] == 0xe0 && (s[1] & 0xe0) == 0x80) || /* overlong? */
          (s[0] == 0xed && (s[1] & 0xe0) == 0xa0) || /* surrogate? */
          (s[0] == 0xef && s[1] == 0xbf &&
           (s[2] & 0xfe) == 0xbe)) /* U+FFFE or U+FFFF? */
        return s;
      else
        s += 3;
    } else if ((s[0] & 0xf8) == 0xf0) {
      /* 11110XXX 10XXxxxx 10xxxxxx 10xxxxxx */
      if ((s[1] & 0xc0) != 0x80 || (s[2] & 0xc0) != 0x80 ||
          (s[3] & 0xc0) != 0x80 ||
          (s[0] == 0xf0 && (s[1] & 0xf0) == 0x80) ||    /* overlong? */
          (s[0] == 0xf4 && s[1] > 0x8f) || s[0] > 0xf4) /* > U+10FFFF? */
        return s;
      else
        s += 4;
    } else
      return s;
  }

  return NULL;
}

static inline FStar_Pervasives_Native_option__Prims_string
FStar_Bytes_iutf8_opt(FStar_Bytes_bytes b) {
  char *str = malloc(b.length + 1);
  CHECK(str);
  memcpy(str, b.data, b.length);
  str[b.length] = 0;

  unsigned const char *err = utf8_check((unsigned char *)str);
  if (err != NULL) {
    FStar_Pervasives_Native_option__Prims_string ret = {
      .tag = FStar_Pervasives_Native_None
    };
    return ret;
  } else {
    FStar_Pervasives_Native_option__Prims_string ret = {
      .tag = FStar_Pervasives_Native_Some, { .case_Some = { .v = str } }
    };
    return ret;
  }
}

static inline bool
__eq__FStar_Bytes_bytes(FStar_Bytes_bytes x0, FStar_Bytes_bytes x1) {
  if (x0.length != x1.length)
    return false;
  for (size_t i = 0; i < x0.length; ++i)
    if (x0.data[i] != x1.data[i])
      return false;
  return true;
}

#endif
#endif
