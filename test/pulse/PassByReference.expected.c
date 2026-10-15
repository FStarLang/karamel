/* krml header omitted for test repeatability */


#include "PassByReference.h"

void PassByReference_make(int32_t a, PassByReference_foo *ret)
{
  *ret = ((PassByReference_foo){ .a = a, .b = 0 });
}

int32_t PassByReference_read(const PassByReference_foo *x)
{
  return x->a;
}

int32_t PassByReference_forward(const PassByReference_foo *x)
{
  return PassByReference_read(x);
}

void PassByReference_assign(PassByReference_foo *p, int32_t a)
{
  PassByReference_make(a, p);
}

void PassByReference_assign_zero(PassByReference_foo *p, int32_t a)
{
  PassByReference_make(a, &p[0U]);
}

void PassByReference_assign_middle(PassByReference_foo *p, int32_t a)
{
  PassByReference_make(a, &p[2U]);
}

int32_t PassByReference_read_value(const PassByReference_foo *x)
{
  return x->a;
}

int32_t PassByReference_read_ref(PassByReference_foo *p)
{
  return PassByReference_read_value(p);
}

int32_t PassByReference_read_zero(PassByReference_foo *p)
{
  return PassByReference_read_value(&p[0U]);
}

