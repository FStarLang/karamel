/* Garbage-collected fat pointers that keep track of their lengths. */
#ifndef __KREMBYTES_H
#ifndef __FStar_H
#define __KREMBYTES_H

#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <inttypes.h>
#include <string.h>

#include "Prims.h"


#include "FStar.h"

typedef uint8_t FStar_Bytes_byte;

/* Copying two words of memory is ok, I guess, when passing around bytes.
 * Alternatively, one could use C99 flexible arrays:
 *
 * typedef struct {
 *   size_t length;
 *   char *data[];
 * }
 */
/* TODO: how to resolve this, this must declared in kremlib.h due to
   circular deps. */


/* typedef struct { */
/*   uint8_t fst, snd; */
/* } K___uint8_t_uint8_t; */

/* typedef struct { */
/*   FStar_Bytes_bytes fst, snd; */
/* } K___FStar_Bytes_bytes_FStar_Bytes_bytes; */

#define CHECK(x) do { \
  if (!(x)) { \
    fprintf(stderr, "malloc failed at %s:%d", __FILE__, __LINE__); \
    exit(253); \
  } \
} while (0)

static inline FStar_Bytes_bytes FStar_Bytes_copy(FStar_Bytes_bytes b1) {
  return b1;
}

static inline krml_checked_int_t FStar_Bytes_length(FStar_Bytes_bytes b) {
  return b.length;
}

static FStar_Bytes_bytes FStar_Bytes_empty_bytes = { .length = 0, .data = NULL };

static inline FStar_Bytes_byte FStar_Bytes_get(FStar_Bytes_bytes b, uint32_t i) {
  return (FStar_Bytes_byte) b.data[i];
}

static inline FStar_Bytes_bytes FStar_Bytes_set_byte(FStar_Bytes_bytes b1, uint32_t i, FStar_Bytes_byte v) {
  uint8_t *data = malloc(b1.length);
  CHECK(data);
  memcpy(data, b1.data, b1.length);
  data[i] = v;
  FStar_Bytes_bytes b2 = { .length = b1.length, data = data };
  return b2;
}

static inline FStar_Bytes_bytes FStar_Bytes_create(uint32_t length, FStar_Bytes_byte initial) {
  uint8_t *data = malloc(length);
  CHECK(data);
  memset(data, initial, length);
  FStar_Bytes_bytes b = { .length = length, .data = data };
  return b;
}

static inline FStar_Bytes_bytes FStar_Bytes_init(uint32_t length, FStar_Bytes_byte (*initial)(uint32_t i)) {
  uint8_t *data = malloc(length);
  CHECK(data);
  for (uint32_t i = 0; i < length; ++i)
    data[i] = initial(i);
  FStar_Bytes_bytes b = { .length = length, .data = data };
  return b;
}

static inline FStar_Bytes_bytes FStar_Bytes_abyte(FStar_Bytes_byte v1) {
  uint8_t * data = (uint8_t*)malloc(1);
  CHECK(data);
  data[0] = v1;
  FStar_Bytes_bytes b = { .length = 1, .data = data };
  return b;
}

static inline FStar_Bytes_bytes FStar_Bytes_twobytes(K___uint8_t_uint8_t v) {
  uint8_t * data = malloc(2);
  CHECK(data);
  data[0] = v.fst;
  data[1] = v.snd;
  FStar_Bytes_bytes b = { .length = 2, .data = data };
  return b;
}

static inline FStar_Bytes_bytes FStar_Bytes_append(FStar_Bytes_bytes b1, FStar_Bytes_bytes b2) {
  // Overflow check
  uint32_t length = Prims_op_Addition(b1.length, b2.length);
  uint8_t * data = (uint8_t*)malloc(length);
  CHECK(data);
  memcpy(data, b1.data, b1.length);
  memcpy(data + b1.length, b2.data, b2.length);
  FStar_Bytes_bytes b = { .length = length, .data = data };
  return b;
}

static inline FStar_Bytes_bytes FStar_Bytes_slice(FStar_Bytes_bytes b1, uint32_t s, uint32_t e) {
  if (s == e)
    return FStar_Bytes_empty_bytes;
  if (s > e)
    exit(254);
  uint32_t length = e - s;
  uint8_t * data = malloc(length);
  CHECK(data);
  memcpy(data, b1.data + s, length);
  FStar_Bytes_bytes b = { .length = length, .data = data };
  return b;
}

static inline FStar_Bytes_bytes FStar_Bytes_sub(FStar_Bytes_bytes b1, uint32_t s, uint32_t l) {
  return FStar_Bytes_slice(b1, s, Prims_op_Addition(s, l));
}

static inline FStar_Bytes_bytes FStar_Bytes_utf8_encode(const char *str) {
  // Note: the const char * helps ensuring that this is a string literal.
  // Strings in F* are UTF8-compatible already so this just writes out utf8
  // bytes in the string literal in C (TODO: check).
  // Assuming that there's no \0 in the string literal. TODO enforce at the F*
  // level.
  FStar_Bytes_bytes b = { .length = strlen(str), .data = (const uint8_t*)str };
  return b;
}

static inline K___FStar_Bytes_bytes_FStar_Bytes_bytes FStar_Bytes_split(FStar_Bytes_bytes bs, FStar_UInt32_t i) {
   K___FStar_Bytes_bytes_FStar_Bytes_bytes p = { .fst = FStar_Bytes_slice(bs, 0, i),
                                                 .snd = FStar_Bytes_slice(bs, i, bs.length) };
   /* printf("split({length=%d; ...}, %d) = ({length=%d, ...}, {length=%d, ...})", */
   /*        bs.length, i, p.fst.length, p.snd.length); */
   return p;
}

static inline FStar_UInt32_t FStar_Bytes_len(FStar_Bytes_bytes b1) {
  return b1.length;
}

static inline FStar_Bytes_bytes FStar_Bytes_bytes_of_int(krml_checked_int_t k, krml_checked_int_t n) {
  /* fprintf(stderr, "Start bytes_of_int (%d, %d)\n", k, n); */
  /* fflush(stderr); */
  FStar_Bytes_bytes b = FStar_Bytes_create(k, 0);
  uint8_t *data = (uint8_t*)b.data;
  for (int i = k - 1; i >= 0; i--) {
    uint32_t offset = 8 * ((k - 1) - i);
    data[i] = (n >> offset) & 0xFF;
  }
  /* fprintf(stderr, "Done with bytes_of_int\n"); */
  /* print_bytes(b.data, b.length); */
  /* fflush(stderr); */
  /* fflush(stdout); */
  return b;
}

static inline krml_checked_int_t FStar_Bytes_int_of_bytes(FStar_Bytes_bytes bs) {
  /* fprintf(stderr, "int_of_bytes\n"); */
  /* print_bytes(bs.data, bs.length); */
  /* fflush(stderr); */
  /* fflush(stdout); */
  krml_checked_int_t res = 0;
  for (uint32_t i = 0 ; i < bs.length ; i++) {
    res <<= 8;
    res |= bs.data[i];
  }
  /* fprintf(stderr, "Done with int_of_bytes %d\n", res); */
  /* fflush(stderr);   */
  return res;
}

static inline int FStar_Bytes_repr_bytes(Prims_nat bs) {
  return bs;
}

static inline FStar_Bytes_bytes FStar_Bytes_xor(FStar_UInt32_t x, FStar_Bytes_bytes b1, FStar_Bytes_bytes b2) {
  fprintf(stderr, "!!TODO xor\n");
  FStar_Bytes_bytes b = { .length = 0ul, .data = NULL }; //placeholder!
  return b;
}


static inline FStar_Bytes_bytes FStar_Bytes_bytes_of_hex(Prims_string str) {
  fprintf(stderr, "!!TODO bytes_of_hex\n");
  FStar_Bytes_bytes b = { .length = 0ul, .data = NULL }; //placeholder!
  return b;
}

static inline Prims_string FStar_Bytes_print_bytes(FStar_Bytes_bytes s) {
  fprintf(stderr, "!!TODO print_bytes\n");
  return NULL; //placeholder!
}

// FIXME this is a correct, but incomplete function that only works if the bytes
// were ASCII in the first place
static inline FStar_Pervasives_Native_option__Prims_string FStar_Bytes_iutf8_opt(FStar_Bytes_bytes b) {
  bool ascii = true;
  for (size_t i = 0; i < b.length; ++i) {
    if (b.data[i] >= 128) {
      ascii = false;
      break;
    }
  }
  if (!ascii) {
    fprintf(stderr, "!!FIXME, non-ASCII string passed to iutf8_opt, do actual "
      "UTF8 detection\n");
    FStar_Pervasives_Native_option__Prims_string ret = {
      .tag = FStar_Pervasives_Native_None
    };
    return ret;
  }
  char *str = malloc(b.length + 1);
  memcpy(str, b.data, b.length);
  str[b.length] = 0;
  FStar_Pervasives_Native_option__Prims_string ret = {
    .tag = FStar_Pervasives_Native_Some,
    .val = { .case_Some = { .v = str } }
  };
  return ret;
}

static inline bool __eq__FStar_Bytes_bytes(FStar_Bytes_bytes x0, FStar_Bytes_bytes x1) {
  if (x0.length != x1.length) return false;
  for (uint32_t i = 0; i < x0.length; ++i) {
    if (x0.data[i] != x1.data[i]) return false;
  }
  return true;
}


#endif
#endif
