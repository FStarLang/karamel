/* krml header omitted for test repeatability */


#include "BoolMatches.h"

bool BoolMatches_and_false(bool (*i)(void))
{
  if (i() && false)
    return true;
  else
    return false;
}

bool BoolMatches_or_true(bool (*i)(void))
{
  if (i() || true)
    return true;
  else
    return false;
}

bool BoolMatches_nested_or(bool (*i)(void))
{
  if (i() && false || true)
    return true;
  else
    return false;
}

bool BoolMatches_nested_and(bool (*i)(void))
{
  if ((i() || true) && false)
    return true;
  else
    return false;
}

bool BoolMatches_pure_and(bool b)
{
  KRML_MAYBE_UNUSED_VAR(b);
  return false;
}

bool BoolMatches_pure_or(bool b)
{
  KRML_MAYBE_UNUSED_VAR(b);
  return true;
}

