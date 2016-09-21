#include <stdlib.h>
#include <stdio.h>
#include <inttypes.h>

extern void ML16Externals_print_int32(int32_t x) {
  printf("%"PRId32"\n", x);
}
