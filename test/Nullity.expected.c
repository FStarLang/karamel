/* krml header omitted for test repeatability */


#include "Nullity.h"

uint32_t read(uint32_t *p)
{
  return *p;
}

void read_unit(void)
{

}

uint32_t read_field(pair *p)
{
  return p->first;
}

int32_t main(void)
{
  return 0;
}

