/* krml header omitted for test repeatability */


#include "DerefZero.h"

uint32_t DerefZero_zero_for_deref = 0U;

uint32_t DerefZero_direct(void)
{
  return 0U;
}

uint32_t DerefZero_aliased(void)
{
  return DerefZero_zero_for_deref;
}

uint32_t DerefZero_add(uint32_t x)
{
  return x + 0U;
}

static DerefZero_pair zeros = { .a = 0U, .b = 0U };

uint32_t DerefZero_record_field(void)
{
  return zeros.a;
}

