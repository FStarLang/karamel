#include <stdlib.h>
#include <stdbool.h>

#include "C.h"

intptr_t nullptr = (intptr_t) NULL;

bool __eq__C_char(char c1, char c2) {
  return c1 == c2;
}

void print_bytes(uint8_t *b, uint32_t len) {
  uint32_t i;
  for (i = 0; i < len; i++){
    printf("%02x", b[i]);
  }
  printf("\n");
}
