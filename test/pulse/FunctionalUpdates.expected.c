/* krml header omitted for test repeatability */


#include "FunctionalUpdates.h"

void FunctionalUpdates_upd_1_ptr(FunctionalUpdates_foo *p, int32_t z)
{
  p->z = z;
}

void FunctionalUpdates_upd_2_ptr(FunctionalUpdates_foo *p, int32_t y, int32_t z)
{
  FunctionalUpdates_foo x = *p;
  *p = ((FunctionalUpdates_foo){ .a = x.a, .b = x.b, .y = y, .z = z });
}

void FunctionalUpdates_upd_2_seq_ptr(FunctionalUpdates_foo *p, int32_t y, int32_t z)
{
  p->y = y;
  p->z = z;
}

FunctionalUpdates_foo FunctionalUpdates_upd_1_local(FunctionalUpdates_foo x, int32_t z)
{
  FunctionalUpdates_foo p = x;
  FunctionalUpdates_foo old = p;
  p = ((FunctionalUpdates_foo){ .a = old.a, .b = old.b, .y = old.y, .z = z });
  return p;
}

int32_t FunctionalUpdates_upd_1_local_snapshot(FunctionalUpdates_foo x, int32_t z)
{
  FunctionalUpdates_foo p = x;
  FunctionalUpdates_foo old = p;
  p = ((FunctionalUpdates_foo){ .a = old.a, .b = old.b, .y = old.y, .z = z });
  return old.z;
}

FunctionalUpdates_foo
FunctionalUpdates_upd_2_local(FunctionalUpdates_foo x, int32_t y, int32_t z)
{
  FunctionalUpdates_foo p = x;
  FunctionalUpdates_foo old = p;
  p = ((FunctionalUpdates_foo){ .a = old.a, .b = old.b, .y = y, .z = z });
  return p;
}

FunctionalUpdates_foo
FunctionalUpdates_upd_2_seq_local(FunctionalUpdates_foo x, int32_t y, int32_t z)
{
  FunctionalUpdates_foo p = x;
  FunctionalUpdates_foo old = p;
  p = ((FunctionalUpdates_foo){ .a = old.a, .b = old.b, .y = y, .z = old.z });
  FunctionalUpdates_foo old1 = p;
  p = ((FunctionalUpdates_foo){ .a = old1.a, .b = old1.b, .y = old1.y, .z = z });
  return p;
}

FunctionalUpdates_foo FunctionalUpdates_upd_1_local_direct(FunctionalUpdates_foo x, int32_t z)
{
  FunctionalUpdates_foo p = x;
  p = ((FunctionalUpdates_foo){ .a = p.a, .b = p.b, .y = p.y, .z = z });
  return p;
}

FunctionalUpdates_foo FunctionalUpdates_upd_1_array(FunctionalUpdates_foo x, int32_t z)
{
  FunctionalUpdates_foo p = x;
  FunctionalUpdates_foo old = p;
  p = ((FunctionalUpdates_foo){ .a = old.a, .b = old.b, .y = old.y, .z = z });
  return p;
}

void FunctionalUpdates_unchanged(FunctionalUpdates_counters *p)
{
  *p = *p;
}

void
FunctionalUpdates_replace_all(
  FunctionalUpdates_counters *p,
  uint32_t first,
  uint32_t second,
  uint32_t untouched
)
{
  *p = ((FunctionalUpdates_counters){ .first = first, .second = second, .untouched = untouched });
}

void FunctionalUpdates_set_two_constants(FunctionalUpdates_four_counters *p)
{
  FunctionalUpdates_four_counters old = *p;
  *p = ((FunctionalUpdates_four_counters){ .a = 1U, .b = 2U, .c = old.c, .keep = old.keep });
}

void FunctionalUpdates_set_three_constants(FunctionalUpdates_four_counters *p)
{
  *p = ((FunctionalUpdates_four_counters){ .a = 1U, .b = 2U, .c = 3U, .keep = p->keep });
}

void
FunctionalUpdates_set_two_values(FunctionalUpdates_four_counters *p, uint32_t a, uint32_t b)
{
  FunctionalUpdates_four_counters old = *p;
  *p = ((FunctionalUpdates_four_counters){ .a = a, .b = b, .c = old.c, .keep = old.keep });
}

void FunctionalUpdates_read_then_set(FunctionalUpdates_counters *p)
{
  *p =
    ((FunctionalUpdates_counters){ .first = p->second, .second = 42U, .untouched = p->untouched });
}

void FunctionalUpdates_increment_field(FunctionalUpdates_counters *p)
{
  p->first++;
}

void FunctionalUpdates_set_at_offset(FunctionalUpdates_four_counters *p, size_t i)
{
  FunctionalUpdates_four_counters old = p[i + (size_t)1U];
  p[i + (size_t)1U] =
    ((FunctionalUpdates_four_counters){ .a = 1U, .b = 2U, .c = old.c, .keep = old.keep });
  p[i + (size_t)1U].c = 3U;
}

void FunctionalUpdates_swap_snapshot(FunctionalUpdates_counters *p)
{
  FunctionalUpdates_counters old = *p;
  *p =
    (
      (FunctionalUpdates_counters){
        .first = old.second,
        .second = old.first,
        .untouched = old.untouched
      }
    );
}

void FunctionalUpdates_swap_mixed(FunctionalUpdates_counters *p)
{
  FunctionalUpdates_counters old = *p;
  *p =
    (
      (FunctionalUpdates_counters){
        .first = old.second,
        .second = p->first,
        .untouched = old.untouched
      }
    );
}

uint32_t FunctionalUpdates_increment_and_return_old(FunctionalUpdates_counters *p)
{
  FunctionalUpdates_counters old = *p;
  p->first = old.first + 1U;
  return old.first;
}

uint32_t FunctionalUpdates_swap_and_return_old(FunctionalUpdates_counters *p)
{
  FunctionalUpdates_counters old = *p;
  *p =
    (
      (FunctionalUpdates_counters){
        .first = old.second,
        .second = old.first,
        .untouched = old.untouched
      }
    );
  return old.first;
}

void FunctionalUpdates_swap_fields(FunctionalUpdates_counters *p)
{
  *p =
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
  FunctionalUpdates_counters old = *p;
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

void FunctionalUpdates_set_at_index(FunctionalUpdates_counters *p, size_t i, uint32_t value)
{
  p[i].first = value;
}

uint32_t
FunctionalUpdates_set_at_index_and_return(
  FunctionalUpdates_counters *p,
  size_t i,
  uint32_t value
)
{
  FunctionalUpdates_counters old = p[i];
  p[i].first = value;
  return old.first;
}

uint32_t
FunctionalUpdates_copy_index(FunctionalUpdates_counters *p, size_t i, size_t j, uint32_t value)
{
  FunctionalUpdates_counters old = p[i];
  p[j] =
    (
      (FunctionalUpdates_counters){
        .first = value,
        .second = old.second,
        .untouched = old.untouched
      }
    );
  return old.first;
}

void
FunctionalUpdates_copy_index_terminal(
  FunctionalUpdates_counters *p,
  size_t i,
  size_t j,
  uint32_t value
)
{
  FunctionalUpdates_counters old = p[i];
  p[j] =
    (
      (FunctionalUpdates_counters){
        .first = value,
        .second = old.second,
        .untouched = old.untouched
      }
    );
}

void FunctionalUpdates_clobber(FunctionalUpdates_counters *p)
{
  FunctionalUpdates_counters old = *p;
  p->first = old.second;
}

void
FunctionalUpdates_not_even_with_a_single_field(
  FunctionalUpdates_counters *p,
  uint32_t (*f)(void)
)
{
  FunctionalUpdates_counters old = *p;
  *p =
    (
      (FunctionalUpdates_counters){ .first = f(), .second = old.second, .untouched = old.untouched }
    );
}

void FunctionalUpdates_unused_buffer(size_t n)
{
  KRML_CHECK_SIZE(sizeof (uint32_t), n);
  uint32_t buf[n];
  KRML_MAYBE_UNUSED_VAR(buf);
}

uint32_t FunctionalUpdates_increment(uint32_t *p)
{
  uint32_t old = *p;
  *p = old + 1U;
  return old;
}

uint32_t FunctionalUpdates_read_before_call(uint32_t initial)
{
  uint32_t cell = initial;
  uint32_t before = cell;
  FunctionalUpdates_increment(&cell);
  return before;
}

uint32_t FunctionalUpdates_call_before_read(uint32_t initial)
{
  uint32_t cell = initial;
  uint32_t before = cell;
  uint32_t result = FunctionalUpdates_increment(&cell);
  return before + result + cell;
}

uint32_t FunctionalUpdates_increment_snapshot(uint32_t *p)
{
  uint32_t buf = *p;
  FunctionalUpdates_increment(&buf);
  return *p;
}

FunctionalUpdates_counters FunctionalUpdates_local_swap_alias(uint32_t first, uint32_t second)
{
  FunctionalUpdates_counters cell = { .first = first, .second = second, .untouched = 17U };
  cell =
    (
      (FunctionalUpdates_counters){
        .first = cell.second,
        .second = cell.first,
        .untouched = cell.untouched
      }
    );
  return cell;
}

FunctionalUpdates_indexed_counters FunctionalUpdates_local_index_alias(void)
{
  KRML_CHECK_SIZE(sizeof (FunctionalUpdates_indexed_counters), (size_t)2U);
  FunctionalUpdates_indexed_counters cell[2U];
  for (uint32_t _i = 0U; _i < (size_t)2U; ++_i)
    cell[_i] =
      ((FunctionalUpdates_indexed_counters){ .index = (size_t)0U, .value = 0U, .spare = 17U });
  cell[cell[0U].index] =
    (
      (FunctionalUpdates_indexed_counters){
        .index = (size_t)1U,
        .value = 2U,
        .spare = cell[cell[0U].index].spare
      }
    );
  return cell[0U];
}

void FunctionalUpdates_nested_update(FunctionalUpdates_nested_record *p)
{
  p->fields =
    ((FunctionalUpdates_nested_fields){ .left = p->fields.left + 1U, .right = p->fields.right });
}

FunctionalUpdates_nested_record
FunctionalUpdates_nested_update_local(FunctionalUpdates_nested_record initial, uint32_t value)
{
  FunctionalUpdates_nested_record p = initial;
  p =
    (
      (FunctionalUpdates_nested_record){
        .fields = { .left = value, .right = p.fields.right },
        .tag = p.tag
      }
    );
  return p;
}

