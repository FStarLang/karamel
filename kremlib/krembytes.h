/* Garbage-collected fat pointers that keep track of their lengths. */
#ifndef __KREMBYTES_H
#define __KREMBYTES_H

#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>
#include <string.h>

#include "kremlib.h"
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
typedef struct {
  uint32_t length;
  char *data;
} FStar_Bytes_bytes;

#define CHECK(x) do { \
  if (!(x)) { \
    fprintf(stderr, "malloc failed at %s:%d", __FILE__, __LINE__); \
    exit(253); \
  } \
} while (0)

static inline FStar_Bytes_bytes FStar_Bytes_copy(FStar_Bytes_bytes b1) {
  char *data = malloc(b1.length);
  memcpy(data, b1.data, b1.length);
  FStar_Bytes_bytes b2 = { .length = b1.length, data = data };
  return b2;
}

static inline krml_checked_int_t FStar_Bytes_length(FStar_Bytes_bytes b) {
  return b.length;
}

static inline FStar_Bytes_bytes FStar_Bytes_empty_bytes = { .length = 0, .data = NULL };

static inline FStar_Bytes_byte FStar_Bytes_get(FStar_Bytes_bytes b, uint32_t i) {
  return (FStar_Bytes_byte) b.data[i];
}

static inline FStar_Bytes_bytes FStar_Bytes_set_byte(FStar_Bytes_bytes b1, uint32_t i, FStar_Byte_byte v) {
  FStar_Bytes_bytes b2 = FStar_Bytes_copy(b1);
  b2.data[i] = (char) v;
  return b2;
}

static inline FStar_Bytes_byte FStar_Bytes_create(uint32_t length, FStar_Byte_byte initial) {
  char *data = malloc(length);
  CHECK(data);
  memset(data, initial, length);
  FStar_Bytes_bytes b = { .length = length, .data = data };
  return b;
}

static inline FStar_Bytes_byte FStar_Bytes_init(uint32_t length, FStar_Byte_byte (*initial)(uint32_t i)) {
  char *data = malloc(length);
  CHECK(data);
  for (uint32_t i = 0; i < length; ++i)
    data[i] = initial(i);
  FStar_Bytes_bytes b = { .length = length, .data = data };
  return b;
}

static inline FStar_Bytes_byte FStar_Bytes_abyte(FStar_Byte_byte v1) {
  FStar_Bytes_bytes b = { .length = 1, .data = malloc(1) };
  CHECK(b.data);
  b.data[0] = v1;
  return b;
}

static inline FStar_Bytes_byte FStar_Bytes_twobytes(K___uint8_t_uint8_t v) {
  FStar_Bytes_bytes b = { .length = 2, .data = malloc(2) };
  CHECK(b.data);
  b.data[0] = v.fst;
  b.data[1] = v.snd;
  return b;
}

static inline FStar_Bytes_bytes FStar_Bytes_append(FStar_Bytes_bytes b1, FStar_Bytes_bytes b2) {
  // Overflow check
  uint32_t length = Prims_op_Addition(b1.length, b2.length);
  FStar_Bytes_bytes b = { .length = length, .data = malloc(length) };
  CHECK(b.data);
  memcpy(b.data, b1.data, b1.length);
  memcpy(b.data + b1.length, b2.data, b2.length);
  return b;
}

static inline FStar_Bytes_bytes FStar_Bytes_slice(FStar_Bytes_bytes b1, uint32_t s, uint32_t e) {
  if (s == e)
    return FStar_Bytes_empty_bytes;
  if (s > e)
    exit(254);
  uint32_t length = e - s;
  FStar_Bytes_bytes b = { .length = length, .data = malloc(length) };
  CHECK(b.data);
  memcpy(b.data, b1.data + s, length);
  return b;
}

static inline FStar_Bytes_bytes FStar_Bytes_sub(FStar_Bytes_bytes b1, uint32_t s, uint32_t l) {
  return FStar_Bytes_slice(b1, s, Prims_op_Addition(s, l));
}

#endif
