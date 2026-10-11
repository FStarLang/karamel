/* krml header omitted for test repeatability */


#include "FunctionalUpdates.h"

void FunctionalUpdates_swap_snapshot(FunctionalUpdates_counters *p)
{
  FunctionalUpdates_counters old = p[0U];
  p->first = old.second;
  p->second = old.first;
}

uint32_t FunctionalUpdates_swap_and_return_old(FunctionalUpdates_counters *p)
{
  FunctionalUpdates_counters old = p[0U];
  p->first = old.second;
  p->second = old.first;
  return old.first;
}

void FunctionalUpdates_swap_fields(FunctionalUpdates_counters *p)
{
  p[0U] =
    (
      (FunctionalUpdates_counters){
        .first = p->second,
        .second = p->first,
        .untouched = p->untouched
      }
    );
}

uint32_t FunctionalUpdates_set_and_return_old(FunctionalUpdates_counters *p, uint32_t value)
{
  FunctionalUpdates_counters old = p[0U];
  p->first = value;
  return old.first;
}

uint32_t
FunctionalUpdates_set_and_return_arg(
  FunctionalUpdates_counters *p,
  uint32_t value,
  uint32_t result
)
{
  p->first = value;
  return result;
}

void FunctionalUpdates_set_at_index(FunctionalUpdates_counters *p, uint32_t i, uint32_t value)
{
  p[i].first = value;
}

void FunctionalUpdates_clobber(FunctionalUpdates_counters *p)
{
  p->first = p->second;
}

void
FunctionalUpdates_not_even_with_a_single_field(
  FunctionalUpdates_counters *p,
  uint32_t (*f)(void)
)
{
  FunctionalUpdates_counters old = p[0U];
  p[0U] =
    (
      (FunctionalUpdates_counters){ .first = f(), .second = old.second, .untouched = old.untouched }
    );
}

