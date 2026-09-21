/* krml header omitted for test repeatability */


#include "IntCompare.h"

void IntCompare_comparisons(uint32_t x, uint32_t y, float z)
{
  IntCompare_consume(true);
  IntCompare_consume(false);
  IntCompare_consume(false);
  IntCompare_consume(true);
  IntCompare_consume(false);
  IntCompare_consume(true);
  IntCompare_consume(x == y);
  IntCompare_consume(z == z);
  IntCompare_consume(z != z);
  IntCompare_consume(z < z);
  IntCompare_consume(z <= z);
}

void IntCompare_expressions(uint32_t x, uint32_t y)
{
  IntCompare_consume(true);
  IntCompare_consume(false);
  IntCompare_consume(false);
  IntCompare_consume(true);
  IntCompare_consume(false);
  IntCompare_consume(true);
  IntCompare_consume(true);
  IntCompare_consume(x + 1U == y + 1U);
  IntCompare_consume(x + 1U < x + 2U);
}

uint32_t IntCompare_select(uint32_t x)
{
  return x + 1U;
}

uint32_t IntCompare_select_false(uint32_t x)
{
  return x + 1U;
}

void IntCompare_calls(void)
{
  uint32_t uu____0 = IntCompare_next();
  IntCompare_consume(uu____0 == IntCompare_next());
  uint32_t uu____1 = IntCompare_next();
  IntCompare_consume(uu____1 != IntCompare_next());
  uint32_t uu____2 = IntCompare_next();
  IntCompare_consume(uu____2 < IntCompare_next());
  uint32_t uu____3 = IntCompare_next();
  IntCompare_consume(uu____3 <= IntCompare_next());
  uint32_t uu____4 = IntCompare_next();
  IntCompare_consume(uu____4 > IntCompare_next());
  uint32_t uu____5 = IntCompare_next();
  IntCompare_consume(uu____5 >= IntCompare_next());
}

void IntCompare_nested_calls(void)
{
  uint32_t uu____0 = IntCompare_next() + 1U;
  IntCompare_consume(uu____0 == IntCompare_next() + 1U);
  uint32_t uu____1 = IntCompare_next() + 1U;
  IntCompare_consume(uu____1 < IntCompare_next() + 1U);
}

