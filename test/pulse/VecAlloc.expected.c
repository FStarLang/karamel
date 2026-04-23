/* krml header omitted for test repeatability */


#include "VecAlloc.h"

void VecAlloc_hf(void)
{
  uint32_t *v = KRML_HOST_MALLOC(sizeof (uint32_t) * (size_t)100U);
  if (v != NULL)
    for (uint32_t _i = 0U; _i < (size_t)100U; ++_i)
      v[_i] = 1U;
  KRML_HOST_FREE(v);
}

