/* krml header omitted for test repeatability */


#include "CompoundAssignment.h"

void CompoundAssignment_test(uint32_t *x)
{
  (*x)++;
  (*x)++;
  (*x)--;
  *x = 1U - *x;
  *x *= 2U;
  *x *= 2U;
  *x /= 2U;
  *x %= 2U;
}

void CompoundAssignment_test2(uint32_t *x)
{
  *x = 2U / *x;
}

void CompoundAssignment_test3(uint32_t *x)
{
  *x = 2U % *x;
}

void CompoundAssignment_test_bitwise(uint32_t *x)
{
  *x &= 0x0FU;
  *x |= 0xF0U;
  *x ^= 0xAAU;
  *x <<= 2U;
  *x >>= 1U;
}

