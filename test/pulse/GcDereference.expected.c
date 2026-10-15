/* krml header omitted for test repeatability */


#include "GcDereference.h"

int32_t GcDereference_head(Prims_list__int32_t *xs)
{
  if (xs->tag == Prims_Nil)
    return 0;
  else if (xs->tag == Prims_Cons)
    return xs->hd;
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

