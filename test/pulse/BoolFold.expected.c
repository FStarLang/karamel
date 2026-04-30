/* krml header omitted for test repeatability */


#include "BoolFold.h"

void BoolFold_main(void)
{
  BoolFold_f(true);
  BoolFold_f(false);
  BoolFold_f(true);
  BoolFold_f(true);
  BoolFold_f(false);
  BoolFold_f(false);
  BoolFold_f(true);
  BoolFold_f(false);
}

