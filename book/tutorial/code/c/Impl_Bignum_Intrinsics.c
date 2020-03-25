#include <stdint.h>
#include <x86intrin.h>

#include "Impl_Bignum_Intrinsics.h"

// Note: we include the *generated* header so that we can get basic C-compiler
// type-checking to make sure we have implemented the right function prototypes,
// at least.
uint32_t Impl_Bignum_Intrinsics_add_carry(uint32_t *dst, uint32_t x, uint32_t y, uint32_t c) {
  return _addcarry_u32(c, x, y, dst);
}
