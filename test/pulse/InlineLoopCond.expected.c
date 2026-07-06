/* krml header omitted for test repeatability */


#include "InlineLoopCond.h"

uint32_t InlineLoopCond_test(uint32_t (*f)(void))
{
  uint32_t uu____0 = f();
  while (uu____0 != 0U)
  {

  }
  return 0U;
}

uint32_t InlineLoopCond_test_ok(uint32_t x)
{
  uint32_t uu____0 = x;
  while (uu____0 != 0U)
  {

  }
  return 0U;
}

