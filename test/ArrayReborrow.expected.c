/* krml header omitted for test repeatability */


#include "ArrayReborrow.h"

extern ArrayReborrowData_foo ArrayReborrowData_table[2];

int32_t ArrayReborrow_read(const ArrayReborrowData_foo *x)
{
  return x->a;
}

int32_t ArrayReborrow_deref(void)
{
  return ArrayReborrow_read(ArrayReborrowData_table);
}

int32_t ArrayReborrow_index(void)
{
  return ArrayReborrow_read(&ArrayReborrowData_table[0U]);
}

int32_t ArrayReborrow_reborrow(ArrayReborrowData_foo *p)
{
  return ArrayReborrow_read(p);
}

