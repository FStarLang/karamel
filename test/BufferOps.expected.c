/* krml header omitted for test repeatability */


#include "BufferOps.h"

uint32_t read(uint32_t *p)
{
  return *p;
}

void write(uint32_t *p, uint32_t v)
{
  *p = v;
}

uint64_t read64(uint64_t *p)
{
  return *p;
}

void read_unit(void)
{

}

void write_unit(void)
{

}

void update(pair *p, uint32_t v)
{
  p->first = v;
}

void update_from_array(pair *p, uint32_t v)
{
  p->first = v;
}

void update_to_array(pair *p, uint32_t v)
{
  p[0U].first = v;
}

uint32_t apply_reader(uint32_t (*f)(uint32_t *x0), uint32_t *p)
{
  return f(p);
}

void apply_writer(void (*f)(uint32_t *x0, uint32_t x1), uint32_t *p, uint32_t v)
{
  f(p, v);
}

static uint32_t op_Bang_Star__uint32_t(uint32_t *p)
{
  return p[0U];
}

uint32_t read_indirect(uint32_t *p)
{
  return apply_reader(op_Bang_Star__uint32_t, p);
}

static void op_Star_Equals__uint32_t(uint32_t *p, uint32_t v)
{
  p[0U] = v;
}

void write_indirect(uint32_t *p, uint32_t v)
{
  apply_writer(op_Star_Equals__uint32_t, p, v);
}

void write_curried(uint32_t *p, uint32_t v)
{
  *p = v;
}

uint32_t *destination(uint32_t *count, uint32_t *p)
{
  (*count)++;
  return p;
}

uint32_t read_effectful(uint32_t *count, uint32_t *p)
{
  return *destination(count, p);
}

void write_effectful(uint32_t *count, uint32_t *p, uint32_t v)
{
  *destination(count, p) = v;
}

uint32_t read_poly__uint32_t(uint32_t *p)
{
  return *p;
}

int32_t main(void)
{
  uint32_t p = 1U;
  write(&p, 2U);
  uint32_t direct = read(&p);
  write_indirect(&p, 3U);
  uint32_t indirect = read_indirect(&p);
  write_curried(&p, 4U);
  uint32_t curried = read_poly__uint32_t(&p);
  uint32_t count = 0U;
  write_effectful(&count, &p, 5U);
  uint32_t effectful = read_effectful(&count, &p);
  uint32_t calls = count;
  pair q = { .first = 11U, .second = 22U };
  update(&q, 33U);
  pair a = q;
  update_from_array(&q, 44U);
  pair b = q;
  update_to_array(&q, 55U);
  pair c = q;
  uint64_t wide = 123ULL;
  uint64_t wide_value = read64(&wide);
  bool
  ok =
    direct == 2U && indirect == 3U && curried == 4U && effectful == 5U && calls == 2U &&
      a.first == 33U
    && a.second == 22U
    && b.first == 44U
    && b.second == 22U
    && c.first == 55U
    && c.second == 22U
    && wide_value == 123ULL;
  return ok ? 0 : 1;
}

