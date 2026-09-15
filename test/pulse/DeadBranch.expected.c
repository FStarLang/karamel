/* krml header omitted for test repeatability */


#include "DeadBranch.h"

krml_checked_int_t DeadBranch_impure(krml_checked_int_t x)
{
  return x;
}

krml_checked_int_t DeadBranch_foo(bool b, krml_checked_int_t x, krml_checked_int_t y)
{
  if (b)
    return DeadBranch_impure(x);
  else
    return DeadBranch_impure(y);
}

krml_checked_int_t DeadBranch_foo1(krml_checked_int_t x, krml_checked_int_t y)
{
  KRML_MAYBE_UNUSED_VAR(y);
  return DeadBranch_impure(x);
}

krml_checked_int_t DeadBranch_foo2(krml_checked_int_t x, krml_checked_int_t y)
{
  KRML_MAYBE_UNUSED_VAR(x);
  return DeadBranch_impure(y);
}

krml_checked_int_t DeadBranch_foo3(krml_checked_int_t x)
{
  if (x != 0)
    return DeadBranch_impure(0);
  else
    return DeadBranch_impure(x);
}

