/* krml header omitted for test repeatability */


#include "LoopBreaks.h"

void LoopBreaks_break_in_switch(uint32_t x)
{
  while (true)
    switch (x)
    {
      case 0U:
        {
          goto loop_exit0;
        }
      case 1U:
        {
          while (true)
            break;
          break;
        }
      default:
        {
          goto loop_exit0;
        }
    }
  loop_exit0: ;
}

