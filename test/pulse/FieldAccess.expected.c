/* krml header omitted for test repeatability */


#include "FieldAccess.h"

int32_t FieldAccess_read(FieldAccess_foo *p)
{
  return p->a;
}

void FieldAccess_update(FieldAccess_foo *p, int32_t a)
{
  p->a = a;
}

