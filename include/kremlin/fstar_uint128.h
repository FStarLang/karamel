#ifndef __KREMLIN_INT128_H
#define __KREMLIN_INT128_H

#include "kremlin/internal/target.h"
#include "kremlin/c_endianness.h"
#include "kremlin/fstar_ints.h"

/******************************************************************************/
/* Machine integers (128-bit arithmetic)                                      */
/******************************************************************************/

/* This header makes KreMLin-generated C code work with:
 * - the default setting where we assume the target compiler define __int128
 * - the setting where we use FStar.UInt128's implementation instead, a.k.a.
 *   "-fnouint128"; in that case, generated C files must be compiled with
 *   -DKRML_NOUINT128, which KreMLin does automatically
 * - a refinement of the case above, wherein all structures are passed by
 *   reference, a.k.a. "-fnostruct-passing", meaning that the KreMLin-generated
 *   must be compiled with -DKRML_NOSTRUCT_PASSING
 */

// Access 64-bit fields within the int128.
// The headers below may override these default macros
#define HIGH64_OF(x) ((x)->high)
#define LOW64_OF(x)  ((x)->low)
 
#if !defined(KRML_NOUINT128)
#  if defined(_MSC_VER)
#    include "kremlin/fstar_uint128_msvc.h"
#  else
#    include "kremlin/fstar_uint128_builtin.h"
#  endif
#else /* !defined(KRML_NOUINT128) */
#  if defined(KRML_SEPARATE_UINT128)
#      include <FStar_UInt128.h>
#  else
    /* This is a bad circular dependency... should fix it properly. */
#      include "FStar.h"
#  endif

typedef FStar_UInt128_uint128 FStar_UInt128_t_, uint128_t;

/* A series of definitions written using pointers. */
static inline void print128_(const char *where, uint128_t *n) {
  KRML_HOST_PRINTF(
      "%s: [0x%08" PRIx64 ",0x%08" PRIx64 "]\n", where, HIGH64_OF(n), LOW64_OF(n));
}

static inline void load128_le_(uint8_t *b, uint128_t *r) {
  LOW64_OF(r) = load64_le(b);
  HIGH64_OF(r) = load64_le(b + 8);
}

static inline void store128_le_(uint8_t *b, uint128_t *n) {
  store64_le(b, LOW64_OF(n));
  store64_le(b + 8, HIGH64_OF(n));
}

static inline void load128_be_(uint8_t *b, uint128_t *r) {
  HIGH64_OF(r) = load64_be(b);
  LOW64_OF(r) = load64_be(b + 8);
}

static inline void store128_be_(uint8_t *b, uint128_t *n) {
  store64_be(b, HIGH64_OF(n));
  store64_be(b + 8, LOW64_OF(n));
}

static inline void
FStar_Int_Cast_Full_uint64_to_uint128_(uint64_t x, uint128_t *dst) {
  /* C89 */
  LOW64_OF(dst) = x;
  HIGH64_OF(dst) = 0;
}

static inline uint64_t FStar_Int_Cast_Full_uint128_to_uint64_(uint128_t *x) {
  return LOW64_OF(x->low);
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

static inline void store128_le(uint8_t *b, uint128_t n) {
  store128_le_(b, &n);
}

static inline uint128_t load128_be(uint8_t *b) {
  uint128_t r;
  load128_be_(b, &r);
  return r;
}

static inline void store128_be(uint8_t *b, uint128_t n) {
  store128_be_(b, &n);
}

static inline uint128_t FStar_Int_Cast_Full_uint64_to_uint128(uint64_t x) {
  uint128_t dst;
  FStar_Int_Cast_Full_uint64_to_uint128_(x, &dst);
  return dst;
}

static inline uint64_t FStar_Int_Cast_Full_uint128_to_uint64(uint128_t x) {
  return FStar_Int_Cast_Full_uint128_to_uint64_(&x);
}

#    else /* !defined(KRML_STRUCT_PASSING) */

#      define print128 print128_
#      define load128_le load128_le_
#      define store128_le store128_le_
#      define load128_be load128_be_
#      define store128_be store128_be_
#      define FStar_Int_Cast_Full_uint128_to_uint64                            \
        FStar_Int_Cast_Full_uint128_to_uint64_
#      define FStar_Int_Cast_Full_uint64_to_uint128                            \
        FStar_Int_Cast_Full_uint64_to_uint128_

#    endif /* KRML_STRUCT_PASSING */
#  endif   /* KRML_UINT128 */

#endif
