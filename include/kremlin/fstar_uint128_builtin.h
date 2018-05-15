#ifndef __KREMLIN_INT128_BUILTIN_H
#define __KREMLIN_INT128_BUILTIN_H

// FStar.UInt128 support for C compilers with a built-in __int128 type.

typedef unsigned __int128 FStar_UInt128_t, FStar_UInt128_t_, uint128_t,
    FStar_UInt128_uint128;

static inline void print128(const char *where, uint128_t n) {
  KRML_HOST_PRINTF(
      "%s: [%" PRIu64 ",%" PRIu64 "]\n", where, (uint64_t)(n >> 64),
      (uint64_t)n);
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

static inline uint128_t FStar_Int_Cast_Full_uint64_to_uint128(uint64_t x) {
  return x;
}

static inline uint64_t FStar_Int_Cast_Full_uint128_to_uint64(uint128_t x) {
  return x;
}

#endif
