#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>

#include "Server.h"

uint32_t bufstrcpy(char *dst, const char *src) {
  /* The F* precondition guarantees that src is zero-terminated */
  return sprintf(dst, "%s", src);
}

uint32_t print_u32(char *dst, uint32_t i) {
  return sprintf(dst, "%"PRIu32, i);
}
