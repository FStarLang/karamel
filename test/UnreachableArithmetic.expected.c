/* krml header omitted for test repeatability */


#include "UnreachableArithmetic.h"

bool and_div_aux(uint32_t x)
{
  return false;
}

bool or_div_aux(uint32_t x)
{
  return true;
}

uint32_t guarded_div_aux(uint32_t x)
{
  return x != 0U ? 1U / x : 2U;
}

bool and_div(void)
{
  return false;
}

bool or_div(void)
{
  return true;
}

uint32_t guarded_div(void)
{
  return 0U != 0U ? 1U / 0U : 2U;
}

bool live_div(void)
{
  return 3U == 0U;
}

bool and_mod_aux(uint32_t x)
{
  return false;
}

bool or_mod_aux(uint32_t x)
{
  return true;
}

uint32_t guarded_mod_aux(uint32_t x)
{
  return x != 0U ? 1U % x : 2U;
}

bool and_mod(void)
{
  return false;
}

bool or_mod(void)
{
  return true;
}

uint32_t guarded_mod(void)
{
  return 0U != 0U ? 1U % 0U : 2U;
}

bool live_mod(void)
{
  return 0U == 0U;
}

int32_t main(void)
{
  if
  (
    !and_div() && or_div() && guarded_div() == 2U && !live_div() && !and_mod() && or_mod() &&
      guarded_mod() == 2U
    && live_mod()
  )
    return 0;
  else
    return 1;
}

