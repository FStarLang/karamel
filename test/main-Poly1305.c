#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <inttypes.h>

typedef __int128 FStar_UInt128_t;
typedef void *Prims_pos, *Prims_nat;

uint64_t FStar_UInt64_gte_mask(uint64_t x, uint64_t y) {
  return x >= y ? UINT64_C(0xffffffffffffffff) : 0;
}

uint64_t FStar_UInt64_eq_mask(uint64_t x, uint64_t y) {
  return x == y ? UINT64_C(0xffffffffffffffff) : 0;
}

#include "Poly_Parameters.c"
#include "Poly_Bigint.c"
#include "Poly_Bignum.c"
#include "Poly_Poly1305.c"

int main() {
  return EXIT_SUCCESS;
}
