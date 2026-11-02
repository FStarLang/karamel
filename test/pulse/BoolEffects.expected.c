/* krml header omitted for test repeatability */


#include "BoolEffects.h"

bool BoolEffects_and_false(bool (*i)(void))
{
  return i() && false;
}

bool BoolEffects_or_true(bool (*i)(void))
{
  return i() || true;
}

bool BoolEffects_match_and_false(bool (*i)(void))
{
  if (i() && false)
    return true;
  else
    return false;
}

bool BoolEffects_match_or_true(bool (*i)(void))
{
  if (i() || true)
    return true;
  else
    return false;
}

