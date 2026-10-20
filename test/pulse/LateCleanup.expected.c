/* krml header omitted for test repeatability */


#include "LateCleanup.h"

uint32_t LateCleanup_local_value(uint32_t x)
{
  return x;
}

uint32_t LateCleanup_ingored_value(uint32_t x)
{
  uint32_t cell = x;
  KRML_HOST_IGNORE(&cell);
  return 123U;
}

uint32_t LateCleanup_local_value2(uint32_t x)
{
  uint32_t cell = x;
  cell += 123U;
  return cell;
}

uint32_t LateCleanup_named_value(uint32_t (*f)(void))
{
  return f();
}

uint32_t LateCleanup_effectful_value(uint32_t (*f)(void))
{
  return f();
}

uint32_t LateCleanup_effectful_sequence(uint32_t (*f)(void), uint32_t (*g)(void))
{
  uint32_t result = f();
  KRML_HOST_IGNORE(g());
  return result;
}

uint32_t *LateCleanup_allocated_value(uint32_t x)
{
  uint32_t *buf = KRML_HOST_MALLOC(sizeof (uint32_t));
  if (buf != NULL)
    buf[0U] = x;
  return buf;
}

