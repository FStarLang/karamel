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

uint8_t key[] = {
  0x85, 0xd6, 0xbe, 0x78, 0x57, 0x55, 0x6d, 0x33, 0x7f, 0x44, 0x52, 0xfe, 0x42,
  0xd5, 0x06, 0xa8, 0x01, 0x03, 0x80, 0x8a, 0xfb, 0x0d, 0xb2, 0xfd, 0x4a, 0xbf,
  0xf6, 0xaf, 0x41, 0x49, 0xf5, 0x1b
};
uint8_t *msg = (uint8_t*)"Cryptographic Forum Research Group";
uint8_t expected[] = {
  0xa8, 0x06, 0x1d, 0xc1, 0x30, 0x51, 0x36, 0xc6, 0xc2, 0x2b, 0x8b, 0xaf, 0x0c,
  0x01, 0x27, 0xa9
};

int main() {
  uint8_t hash[16];
  Poly_Poly1305_poly1305_mac(hash, msg, 34, key);
  for (int i = 0; i < 16; ++i) {
    if (hash[i] != expected[i]) {
      fprintf(stderr, "hash and expected differ at byte %d\n", i);
      return EXIT_FAILURE;
    }
  }
  printf("success");
  return EXIT_SUCCESS;
}
