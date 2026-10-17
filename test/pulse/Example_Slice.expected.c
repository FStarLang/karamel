/* krml header omitted for test repeatability */


#include "Example_Slice.h"

typedef struct slice__uint8_t_s
{
  uint8_t *elt;
  size_t len;
}
slice__uint8_t;

static slice__uint8_t from_array__uint8_t(uint8_t *a, size_t alen)
{
  return ((slice__uint8_t){ .elt = a, .len = alen });
}

typedef struct tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t_s
{
  slice__uint8_t _1;
  slice__uint8_t _2;
}
tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t;

static tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
split__uint8_t(slice__uint8_t s, size_t i)
{
  uint8_t *elt_ = s.elt + i;
  slice__uint8_t s1 = { .elt = s.elt, .len = i };
  slice__uint8_t s2 = { .elt = elt_, .len = s.len - i };
  return
    ((tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){ ._1 = s1, ._2 = s2 });
}

static slice__uint8_t subslice__uint8_t(slice__uint8_t s, size_t i, size_t j)
{
  uint8_t *elt_ = s.elt + i;
  return ((slice__uint8_t){ .elt = elt_, .len = j - i });
}

static uint8_t op_Array_Access__uint8_t(slice__uint8_t a, size_t i)
{
  return a.elt[i];
}

static size_t len__uint8_t(slice__uint8_t s)
{
  return s.len;
}

static void op_Array_Assignment__uint8_t(slice__uint8_t a, size_t i, uint8_t v)
{
  a.elt[i] = v;
}

static void copy__uint8_t(slice__uint8_t dst, slice__uint8_t src)
{
  memcpy(dst.elt, src.elt, src.len * sizeof (uint8_t));
}

void Example_Slice_test(uint8_t *arr)
{
  slice__uint8_t slice = from_array__uint8_t(arr, (size_t)6U);
  tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
  s_ = split__uint8_t(slice, (size_t)2U);
  slice__uint8_t s1 = s_._1;
  slice__uint8_t s2 = s_._2;
  slice__uint8_t s2_ = subslice__uint8_t(s2, (size_t)1U, (size_t)4U);
  uint8_t x = op_Array_Access__uint8_t(s2_, len__uint8_t(s1));
  op_Array_Assignment__uint8_t(s1, (size_t)1U, x);
  tuple2__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
  s_1 = split__uint8_t(s2, (size_t)2U);
  slice__uint8_t s3 = s_1._1;
  slice__uint8_t s4 = s_1._2;
  copy__uint8_t(s3, s4);
}

