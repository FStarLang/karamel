/* krml header omitted for test repeatability */


#include "InlineShortCircuit.h"

bool InlineShortCircuit_and_rhs(bool b, bool (*i)(void))
{
  bool uu____0 = i();
  return b && uu____0;
}

bool InlineShortCircuit_or_rhs(bool b, bool (*i)(void))
{
  bool uu____0 = i();
  return b || uu____0;
}

bool InlineShortCircuit_and_lhs(bool b, bool (*i)(void))
{
  return i() && b;
}

bool InlineShortCircuit_or_lhs(bool b, bool (*i)(void))
{
  return i() || b;
}

bool InlineShortCircuit_nested_rhs(bool b, bool c, bool (*i)(void))
{
  bool uu____0 = i();
  return b && (uu____0 || c);
}

bool InlineShortCircuit_nested_lhs(bool b, bool c, bool (*i)(void))
{
  return i() && b || c;
}

bool InlineShortCircuit_and_false(bool (*i)(void))
{
  KRML_HOST_IGNORE(i());
  return false;
}

bool InlineShortCircuit_or_true(bool (*i)(void))
{
  KRML_HOST_IGNORE(i());
  return true;
}

