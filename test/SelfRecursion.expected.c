/* krml header omitted for test repeatability */


#include "internal/SelfRecursion.h"

static uint32_t local(uint32_t n)
{
  if (n == 0U)
    return 0U;
  else
    return local(n - 1U) + 1U;
}

uint32_t entry(uint32_t n)
{
  return local(n);
}

uint32_t public_rec(uint32_t n)
{
  if (n == 0U)
    return 0U;
  else
    return public_rec(n - 1U) + 1U;
}

static uint32_t mutual_first(uint32_t n)
{
  if (n == 0U)
    return 0U;
  else
    return mutual_second(n - 1U) + 1U;
}

uint32_t mutual_second(uint32_t n)
{
  if (n == 0U)
    return 0U;
  else
    return mutual_first(n - 1U) + 1U;
}

uint32_t mutual_entry(uint32_t n)
{
  return mutual_first(n);
}

int32_t main(void)
{
  return 0;
}

