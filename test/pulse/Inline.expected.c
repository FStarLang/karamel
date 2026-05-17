/* krml header omitted for test repeatability */


#include "Inline.h"

uint32_t Inline_basic(uint32_t (*i)(void))
{
  return i();
}

uint32_t Inline_chain(uint32_t (*i)(void), uint32_t (*f)(uint32_t x0))
{
  return f(i());
}

void Inline_chain_ignore(uint32_t (*i)(void), uint32_t (*f)(uint32_t x0))
{
  KRML_HOST_IGNORE(f(i()));
}

void Inline_chain_ignore_(uint32_t (*i)(void), uint32_t (*f)(uint32_t x0))
{
  uint32_t x = f(i());
  KRML_MAYBE_UNUSED_VAR(x);
}

uint32_t Inline_chain_ignore__(uint32_t (*i)(void), uint32_t (*f)(uint32_t x0))
{
  uint32_t uu____0 = f(i());
  Inline_g();
  return uu____0;
}

uint32_t Inline_tst(uint32_t shared)
{
  uint32_t uu____0 = shared / 100U;
  uint32_t i = 0U;
  uint32_t __anf00 = i;
  bool cond = __anf00 < uu____0;
  while (cond)
  {
    uint32_t __anf0 = i;
    i = __anf0 + 1U;
    uint32_t __anf00 = i;
    cond = __anf00 < uu____0;
  }
  return 1U;
}

uint32_t Inline_order(uint32_t (*f)(void))
{
  uint32_t uu____0 = f();
  return uu____0 + Inline_g();
}

uint32_t Inline_test_array_access(uint32_t *a, size_t *r)
{
  return a[*r];
}

