#ifndef __KREMLIN_MACHINEINTS_H
#define __KREMLIN_MACHINEINTS_H

/******************************************************************************/
/* Implementation of machine integers (possibly of 128-bit integers)          */
/******************************************************************************/

/* Integer types */
typedef uint64_t FStar_UInt64_t, FStar_UInt64_t_;
typedef int64_t FStar_Int64_t, FStar_Int64_t_;
typedef uint32_t FStar_UInt32_t, FStar_UInt32_t_;
typedef int32_t FStar_Int32_t, FStar_Int32_t_;
typedef uint16_t FStar_UInt16_t, FStar_UInt16_t_;
typedef int16_t FStar_Int16_t, FStar_Int16_t_;
typedef uint8_t FStar_UInt8_t, FStar_UInt8_t_;
typedef int8_t FStar_Int8_t, FStar_Int8_t_;

static inline uint32_t rotate32_left(uint32_t x, uint32_t n) {
  /*  assert (n<32); */
  return (x << n) | (x >> (-n & 31));
}
static inline uint32_t rotate32_right(uint32_t x, uint32_t n) {
  /*  assert (n<32); */
  return (x >> n) | (x << (-n & 31));
}

/* Constant time comparisons */
static inline uint8_t FStar_UInt8_eq_mask(uint8_t x, uint8_t y) {
  x = ~(x ^ y);
  x &= x << 4;
  x &= x << 2;
  x &= x << 1;
  return (int8_t)x >> 7;
}

static inline uint8_t FStar_UInt8_gte_mask(uint8_t x, uint8_t y) {
  return ~(uint8_t)(((int32_t)x - y) >> 31);
}

static inline uint16_t FStar_UInt16_eq_mask(uint16_t x, uint16_t y) {
  x = ~(x ^ y);
  x &= x << 8;
  x &= x << 4;
  x &= x << 2;
  x &= x << 1;
  return (int16_t)x >> 15;
}

static inline uint16_t FStar_UInt16_gte_mask(uint16_t x, uint16_t y) {
  return ~(uint16_t)(((int32_t)x - y) >> 31);
}

static inline uint32_t FStar_UInt32_eq_mask(uint32_t x, uint32_t y) {
  x = ~(x ^ y);
  x &= x << 16;
  x &= x << 8;
  x &= x << 4;
  x &= x << 2;
  x &= x << 1;
  return ((int32_t)x) >> 31;
}

static inline uint32_t FStar_UInt32_gte_mask(uint32_t x, uint32_t y) {
  return ~((uint32_t)(((int64_t)x - y) >> 63));
}

static inline uint64_t FStar_UInt64_eq_mask(uint64_t x, uint64_t y) {
  x = ~(x ^ y);
  x &= x << 32;
  x &= x << 16;
  x &= x << 8;
  x &= x << 4;
  x &= x << 2;
  x &= x << 1;
  return ((int64_t)x) >> 63;
}

static inline uint64_t FStar_UInt64_gte_mask(uint64_t x, uint64_t y) {
  uint64_t low63 =
      ~((uint64_t)((int64_t)((int64_t)(x & UINT64_C(0x7fffffffffffffff)) -
                             (int64_t)(y & UINT64_C(0x7fffffffffffffff))) >>
                   63));
  uint64_t high_bit =
      ~((uint64_t)((int64_t)((int64_t)(x & UINT64_C(0x8000000000000000)) -
                             (int64_t)(y & UINT64_C(0x8000000000000000))) >>
                   63));
  return low63 & high_bit;
}

/* Platform-specific 128-bit arithmetic. These are static functions in a header,
 * so that each translation unit gets its own copy and the C compiler can
 * optimize. */
#ifndef KRML_NOUINT128
typedef unsigned __int128 FStar_UInt128_t, FStar_UInt128_t_, uint128_t;

static inline void print128(const char *where, uint128_t n) {
  KRML_HOST_PRINTF("%s: [%" PRIu64 ",%" PRIu64 "]\n", where,
                   (uint64_t)(n >> 64), (uint64_t)n);
}

static inline uint128_t load128_le(uint8_t *b) {
  uint128_t l = (uint128_t)load64_le(b);
  uint128_t h = (uint128_t)load64_le(b + 8);
  return (h << 64 | l);
}

static inline void store128_le(uint8_t *b, uint128_t n) {
  store64_le(b, (uint64_t)n);
  store64_le(b + 8, (uint64_t)(n >> 64));
}

static inline uint128_t load128_be(uint8_t *b) {
  uint128_t h = (uint128_t)load64_be(b);
  uint128_t l = (uint128_t)load64_be(b + 8);
  return (h << 64 | l);
}

static inline void store128_be(uint8_t *b, uint128_t n) {
  store64_be(b, (uint64_t)(n >> 64));
  store64_be(b + 8, (uint64_t)n);
}

#  define FStar_UInt128_add(x, y) ((x) + (y))
#  define FStar_UInt128_mul(x, y) ((x) * (y))
#  define FStar_UInt128_add_mod(x, y) ((x) + (y))
#  define FStar_UInt128_sub(x, y) ((x) - (y))
#  define FStar_UInt128_sub_mod(x, y) ((x) - (y))
#  define FStar_UInt128_logand(x, y) ((x) & (y))
#  define FStar_UInt128_logor(x, y) ((x) | (y))
#  define FStar_UInt128_logxor(x, y) ((x) ^ (y))
#  define FStar_UInt128_lognot(x) (~(x))
#  define FStar_UInt128_shift_left(x, y) ((x) << (y))
#  define FStar_UInt128_shift_right(x, y) ((x) >> (y))
#  define FStar_UInt128_uint64_to_uint128(x) ((uint128_t)(x))
#  define FStar_UInt128_uint128_to_uint64(x) ((uint64_t)(x))
#  define FStar_UInt128_mul_wide(x, y) ((uint128_t)(x) * (y))
#  define FStar_UInt128_op_Hat_Hat(x, y) ((x) ^ (y))

static inline uint128_t FStar_UInt128_eq_mask(uint128_t x, uint128_t y) {
  uint64_t mask =
      FStar_UInt64_eq_mask((uint64_t)(x >> 64), (uint64_t)(y >> 64)) &
      FStar_UInt64_eq_mask(x, y);
  return ((uint128_t)mask) << 64 | mask;
}

static inline uint128_t FStar_UInt128_gte_mask(uint128_t x, uint128_t y) {
  uint64_t mask =
      (FStar_UInt64_gte_mask(x >> 64, y >> 64) &
       ~(FStar_UInt64_eq_mask(x >> 64, y >> 64))) |
      (FStar_UInt64_eq_mask(x >> 64, y >> 64) & FStar_UInt64_gte_mask(x, y));
  return ((uint128_t)mask) << 64 | mask;
}

#  else /* !defined(KRML_NOUINT128) */

  /* This is a bad circular dependency... should fix it properly. */
#    include "FStar.h"

typedef FStar_UInt128_uint128 FStar_UInt128_t_, uint128_t;

/* A series of definitions written using pointers. */
static inline void print128_(const char *where, uint128_t *n) {
  KRML_HOST_PRINTF("%s: [0x%08" PRIx64 ",0x%08" PRIx64 "]\n", where, n->high, n->low);
}

static inline void load128_le_(uint8_t *b, uint128_t *r) {
  r->low = load64_le(b);
  r->high = load64_le(b + 8);
}

static inline void store128_le_(uint8_t *b, uint128_t *n) {
  store64_le(b, n->low);
  store64_le(b + 8, n->high);
}

static inline void load128_be_(uint8_t *b, uint128_t *r) {
  r->high = load64_be(b);
  r->low = load64_be(b + 8);
}

static inline void store128_be_(uint8_t *b, uint128_t *n) {
  store64_be(b, n->high);
  store64_be(b + 8, n->low);
}

#    ifndef KRML_NOSTRUCT_PASSING

static inline void print128(const char *where, uint128_t n) {
  print128_(where, &n);
}

static inline uint128_t load128_le(uint8_t *b) {
  uint128_t r;
  load128_le_(b, &r);
  return r;
}

static inline void store128_le(uint8_t *b, uint128_t n) { store128_le_(b, &n); }

static inline uint128_t load128_be(uint8_t *b) {
  uint128_t r;
  load128_be_(b, &r);
  return r;
}

static inline void store128_be(uint8_t *b, uint128_t n) { store128_be_(b, &n); }

#    else /* !defined(KRML_STRUCT_PASSING) */

#      define print128 print128_
#      define load128_le load128_le_
#      define store128_le store128_le_
#      define load128_be load128_be_
#      define store128_be store128_be_

#    endif /* KRML_STRUCT_PASSING */
#  endif   /* KRML_UINT128 */

#endif
