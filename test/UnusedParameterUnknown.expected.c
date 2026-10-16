/* krml header omitted for test repeatability */


#include "UnusedParameterUnknown.h"

#define external_identity(x) (x)

static int32_t forward(int32_t x)
{
  return external_identity(x);
}

int32_t main(void)
{
  if (forward(42) == 42)
    return 0;
  else
    return 1;
}

