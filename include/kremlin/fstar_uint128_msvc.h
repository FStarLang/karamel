#ifndef __FStar_UInt128_MSVC_H
#define __FStar_UInt128_MSVC_H

// FStar.UInt128 support for the MSVC compiler, which does not have an __int128 type.

#ifndef _MSC_VER
#error This file only works with the MSVC compiler
#endif

#include <stdbool.h>
#include <kremlin/fstar_ints.h>

#if defined(_M_X64)
#include <emmintrin.h>
typedef __m128i FStar_UInt128_uint128;

#undef HIGH64_OF
#undef LOW64_OF
#define HIGH64_OF(x) ((x)->m128i_u64[1])
#define LOW64_OF(x)  ((x)->m128i_u64[0])

#else
typedef struct FStar_UInt128_uint128_s
{
  uint64_t low;
  uint64_t high;
}
FStar_UInt128_uint128;
#endif

typedef FStar_UInt128_uint128 FStar_UInt128_t, uint128_t;

static inline void print128(const char *where, FStar_UInt128_uint128 n) {
  KRML_HOST_PRINTF(
      "%s: [%" PRIu64 ",%" PRIu64 "]\n", where, HIGH64_OF(&n),
      LOW64_OF(&n));
}

FStar_UInt128_uint128 load128_le(uint8_t *b);

void store128_le(uint8_t *b, FStar_UInt128_uint128 n);

FStar_UInt128_uint128 load128_be(uint8_t *b);

void store128_be(uint8_t *b, FStar_UInt128_uint128 n);

FStar_UInt128_uint128 FStar_UInt128_add(FStar_UInt128_uint128 a, FStar_UInt128_uint128 b);

FStar_UInt128_uint128 FStar_UInt128_add_mod(FStar_UInt128_uint128 a, FStar_UInt128_uint128 b);

FStar_UInt128_uint128 FStar_UInt128_sub(FStar_UInt128_uint128 a, FStar_UInt128_uint128 b);

FStar_UInt128_uint128 FStar_UInt128_sub_mod(FStar_UInt128_uint128 a, FStar_UInt128_uint128 b);

FStar_UInt128_uint128 FStar_UInt128_logand(FStar_UInt128_uint128 a, FStar_UInt128_uint128 b);

FStar_UInt128_uint128 FStar_UInt128_logxor(FStar_UInt128_uint128 a, FStar_UInt128_uint128 b);

FStar_UInt128_uint128 FStar_UInt128_logor(FStar_UInt128_uint128 a, FStar_UInt128_uint128 b);

FStar_UInt128_uint128 FStar_UInt128_lognot(FStar_UInt128_uint128 a);

FStar_UInt128_uint128 FStar_UInt128_shift_left(FStar_UInt128_uint128 a, uint32_t s);

FStar_UInt128_uint128 FStar_UInt128_shift_right(FStar_UInt128_uint128 a, uint32_t s);

FStar_UInt128_uint128 FStar_UInt128_eq_mask(FStar_UInt128_uint128 a, FStar_UInt128_uint128 b);

FStar_UInt128_uint128 FStar_UInt128_gte_mask(FStar_UInt128_uint128 a, FStar_UInt128_uint128 b);

FStar_UInt128_uint128 FStar_UInt128_uint64_to_uint128(uint64_t a);

uint64_t FStar_UInt128_uint128_to_uint64(FStar_UInt128_uint128 a);

FStar_UInt128_uint128 FStar_UInt128_mul_wide(uint64_t x, uint64_t y);

#define FStar_UInt128_op_Hat_Hat FStar_UInt128_logxor


#define __FStar_UInt128_MSVC_H_DEFINED
#endif
