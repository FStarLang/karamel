#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

// Note: I always include the generated header, that way I get a compilation
// error in my hand-written test if for some reason the signature of a function
// changes. Don't declare extern functions!
#include "Bignum.h"

// Could've been written in Low*, just like this entire file...
Impl_Bignum_t mk_pair(uint32_t length, uint32_t *words) {
  return (Impl_Bignum_t) { .fst = length, .snd = words };
}

int main() {
  uint32_t x[1] = { 0xf14bcc56 };
  uint32_t y[1] = { 0x15dd6819 };
  Impl_Bignum_t r = Impl_Bignum_add_alloc(mk_pair(1, x), mk_pair(1,y));
  if (r.fst != 2 || r.snd[0] != 0x729346f || r.snd[1] != 0x01) {
    printf("Incorrect test!\n");
    return EXIT_FAILURE;
  } else {
    printf("C test OK!\n");
    return EXIT_SUCCESS;
  }
}
