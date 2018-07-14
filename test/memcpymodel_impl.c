#include "MemCpyModel.h"

#include <inttypes.h>
#include <string.h>

void MemCpyModel_memcpy(uint8_t *dst, uint8_t *src, uint32_t count) {
  memcpy(dst, src, count);
}
