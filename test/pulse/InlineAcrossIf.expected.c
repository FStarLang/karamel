/* krml header omitted for test repeatability */


#include "InlineAcrossIf.h"

uint32_t InlineAcrossIf_basic(bool b, uint32_t (*i)(void))
{
  uint32_t uu____0 = i();
  uint32_t y = b ? 2U : 3U;
  return uu____0 + y;
}

uint32_t InlineAcrossIf_basic2(bool b, uint32_t (*i)(void), uint32_t x, uint32_t y)
{
  uint32_t uu____0 = i();
  uint32_t y1 = b ? x : y;
  return uu____0 + y1;
}

uint32_t InlineAcrossIf_basic3(bool b, uint32_t x)
{
  uint32_t uu____0 = x;
  return b ? uu____0 + 1U : uu____0 + 2U;
}

uint32_t InlineAcrossIf_should_not_inline1(bool b, uint32_t (*i1)(void), uint32_t (*i2)(void))
{
  uint32_t uu____0 = i1();
  uint32_t y;
  if (b)
    y = i2();
  else
    y = 0U;
  return uu____0 + y;
}

uint32_t InlineAcrossIf_should_not_inline2(bool b, uint32_t (*i1)(void), uint32_t (*i2)(void))
{
  uint32_t uu____0 = i1();
  uint32_t y;
  if (b)
    y = 0U;
  else
    y = i2();
  return uu____0 + y;
}

uint32_t InlineAcrossIf_should_not_inline3(bool b, uint32_t (*i1)(void), uint32_t (*i2)(void))
{
  KRML_MAYBE_UNUSED_VAR(b);
  uint32_t uu____0 = i1();
  uint32_t y;
  if (i2() == 0U)
    y = 0U;
  else
    y = 1U;
  return uu____0 + y;
}

