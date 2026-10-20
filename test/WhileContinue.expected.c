/* krml header omitted for test repeatability */


#include "WhileContinue.h"

uint32_t WhileContinue_let_condition(uint32_t start)
{
  uint32_t i = start;
  while (true)
  {
    i++;
    if (!(i < 3U))
      break;
    i++;
    continue;
  }
  return i;
}

uint32_t WhileContinue_if_condition(uint32_t start)
{
  uint32_t i = start;
  while (true)
  {
    bool ite;
    if (i < 3U)
    {
      i++;
      ite = true;
    }
    else
      ite = false;
    if (!ite)
      break;
    i++;
    continue;
  }
  return i;
}

