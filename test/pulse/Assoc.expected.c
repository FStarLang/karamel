/* krml header omitted for test repeatability */


#include "Assoc.h"

int32_t Assoc_test_r(int32_t x, int32_t y, int32_t z)
{
  return x + (y + z);
}

int32_t Assoc_test_r_(int32_t x, int32_t y, int32_t z)
{
  return x + (y - z);
}

int32_t Assoc_test_l(int32_t x, int32_t y, int32_t z)
{
  return x + y + z;
}

int32_t Assoc_test_l_(int32_t x, int32_t y, int32_t z)
{
  return x + y - z;
}

int32_t Assoc_test4(int32_t x, int32_t y, int32_t z, int32_t w)
{
  return x + y - (z + w);
}

int32_t Assoc_test4_(int32_t x, int32_t y, int32_t z, int32_t w)
{
  return x - y + (z - w);
}

