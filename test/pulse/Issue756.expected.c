/* krml header omitted for test repeatability */


#include "Issue756.h"

bool Issue756_direct_lt(uint64_t a, uint32_t b)
{
  return (uint32_t)a < b;
}

bool Issue756_direct_eq(uint64_t a, uint32_t b)
{
  return (uint32_t)a == b;
}

bool Issue756_local_lt(uint64_t a, uint32_t b)
{
  uint32_t a32 = (uint32_t)a;
  return a32 < b;
}

bool Issue756_local_eq(uint64_t a, uint32_t b)
{
  uint32_t a32 = (uint32_t)a;
  return a32 == b;
}

