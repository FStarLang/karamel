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

void LoopBreaks_break_once(void)
{
  for (uint32_t i = 0U; i < 1U; i++)
    break;
}

void LoopBreaks_continue_once(void)
{
  for (uint32_t i = 0U; i < 1U; i++)
    continue;
}

void LoopBreaks_break_in_for_match(uint32_t x)
{
  for (uint32_t i = 0U; i < 2U; i++)
    switch (x)
    {
      case 0U:
        {
          goto loop_exit0;
        }
      default:
        {

        }
    }
  loop_exit0: ;
}

void LoopBreaks_continue_in_for_if(bool b)
{
  for (uint32_t i = 0U; i < 2U; i++)
    if (b)
      continue;
}

void LoopBreaks_unroll_around_for(bool b)
{
  for (uint32_t i = 0U; i < 1U; i++)
    if (b)
      break;
    else
      continue;
}

void LoopBreaks_unroll_around_while(void)
{
  while (true)
    break;
}

