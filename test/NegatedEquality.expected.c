/* krml header omitted for test repeatability */


#include "NegatedEquality.h"

bool uint_ne(uint32_t a, uint32_t b)
{
  return a != b;
}

bool uint_eq(uint32_t a, uint32_t b)
{
  return a == b;
}

bool bool_ne(bool a, bool b)
{
  return a != b;
}

bool double_not(uint32_t a, uint32_t b)
{
  return a == b;
}

bool bool_double_not(bool c)
{
  return c;
}

bool conditional_not(uint32_t a, uint32_t b)
{
  return a != b;
}

bool conditional_and(uint32_t a, uint32_t b, bool c)
{
  return a != b && c;
}

bool conditional_or(uint32_t a, uint32_t b, bool c)
{
  return a != b || c;
}

bool uint_ge(uint32_t a, uint32_t b)
{
  return a >= b;
}

bool uint_gt(uint32_t a, uint32_t b)
{
  return a > b;
}

bool uint_le(uint32_t a, uint32_t b)
{
  return a <= b;
}

bool uint_lt(uint32_t a, uint32_t b)
{
  return a < b;
}

bool int_ge(int32_t a, int32_t b)
{
  return a >= b;
}

bool int_gt(int32_t a, int32_t b)
{
  return a > b;
}

bool int_le(int32_t a, int32_t b)
{
  return a <= b;
}

bool int_lt(int32_t a, int32_t b)
{
  return a < b;
}

bool narrow_ne(uint8_t a, uint8_t b)
{
  return (((uint32_t)a + (uint32_t)b) & 0xFFU) != 0U;
}

bool narrow_ge(uint8_t a, uint8_t b, uint8_t c)
{
  return (((uint32_t)a + (uint32_t)b) & 0xFFU) >= (uint32_t)c;
}

bool nonnull(uint32_t *p)
{
  return p != NULL;
}

bool null_again(uint32_t *p)
{
  return p == NULL;
}

bool configured(uint32_t *p, bool enabled)
{
  return (p != NULL) == enabled;
}

void null_else(uint32_t *p)
{
  if (p != NULL)
  {
    p[0U] = 7U;
    return;
  }
}

void nonnull_else(uint32_t *out, uint32_t *p)
{
  if (p == NULL)
  {
    out[0U] = 7U;
    return;
  }
}

uint32_t next(uint32_t *p)
{
  uint32_t n = p[0U] + 1U;
  p[0U] = n;
  return n;
}

bool call_ne(uint32_t *p)
{
  uint32_t a = next(p);
  uint32_t b = next(p);
  return a != b;
}

int32_t main(void)
{
  uint32_t p = 0U;
  bool distinct = call_ne(&p);
  uint32_t count = p;
  return distinct && count == 2U ? 0 : 1;
}

