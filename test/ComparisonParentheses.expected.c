/* krml header omitted for test repeatability */


#include "ComparisonParentheses.h"

bool eq_left(uint32_t a, uint32_t b, bool c)
{
  return (a == b) == c;
}

bool neq_left(uint32_t a, uint32_t b, bool c)
{
  return (a != b) == c;
}

bool lt_left(uint32_t a, uint32_t b, bool c)
{
  return (a < b) == c;
}

bool lte_left(uint32_t a, uint32_t b, bool c)
{
  return (a <= b) == c;
}

bool gt_left(uint32_t a, uint32_t b, bool c)
{
  return (a > b) == c;
}

bool gte_left(uint32_t a, uint32_t b, bool c)
{
  return (a >= b) == c;
}

bool eq_right(bool a, uint32_t b, uint32_t c)
{
  return a != (b == c);
}

bool neq_right(bool a, uint32_t b, uint32_t c)
{
  return a != (b != c);
}

bool lt_right(bool a, uint32_t b, uint32_t c)
{
  return a != (b < c);
}

bool lte_right(bool a, uint32_t b, uint32_t c)
{
  return a != (b <= c);
}

bool gt_right(bool a, uint32_t b, uint32_t c)
{
  return a != (b > c);
}

bool gte_right(bool a, uint32_t b, uint32_t c)
{
  return a != (b >= c);
}

bool null_configured(uint32_t *p, bool enabled)
{
  return (p == NULL) == enabled;
}

bool arithmetic(uint32_t a, uint32_t b, uint32_t c)
{
  return a + b == c;
}

bool logical(uint32_t a, uint32_t b, uint32_t c)
{
  return a < b && b < c;
}

int32_t main(void)
{
  return 0;
}

