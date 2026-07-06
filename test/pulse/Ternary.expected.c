/* krml header omitted for test repeatability */


#include "Ternary.h"

uint32_t Ternary_u32min(uint32_t x, uint32_t y)
{
  return x < y ? x : y;
}

uint32_t Ternary_test2(uint32_t x, uint32_t y, uint32_t w, uint32_t z)
{
  return (x < y ? x : y) + (w < z ? w : z);
}

uint32_t Ternary_u32min__(uint32_t x, uint32_t y)
{
  uint32_t res = x < y ? x : y;
  return res + 1U;
}

uint32_t Ternary_u32min___(uint32_t x, uint32_t y)
{
  return (x < y ? x : y) + 1U;
}

uint32_t Ternary_call(bool b, uint32_t (*f)(void), uint32_t (*g)(void))
{
  if (b)
    return f();
  else
    return g();
}

uint32_t Ternary_u32clamp(uint32_t x, uint32_t lo, uint32_t hi)
{
  return x < lo ? lo : x > hi ? hi : x;
}

bool Ternary_is_in_range(uint32_t x, uint32_t lo, uint32_t hi)
{
  return !(x < lo) && !(x > hi);
}

void Ternary_actual_if(bool b, void (*f)(void), void (*g)(void))
{
  if (b)
    f();
  else
    g();
}

