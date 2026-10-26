/* krml header omitted for test repeatability */


#include "UnaryMinus.h"

int32_t UnaryMinus_double_negation(int32_t x)
{
  return -(-x);
}

int32_t UnaryMinus_negative_constant(void)
{
  return -(-1);
}

