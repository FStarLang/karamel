/* krml header omitted for test repeatability */


#include "GotoReturn.h"

int32_t GotoReturn_early_return_int(int32_t x)
{
  int32_t result = 0;

  if (x == 0)
  {
    result = GotoReturn_opaque_int32(42);
    goto exit;
  }

  if (x == 1)
  {
    result = GotoReturn_opaque_int32(43);
    goto exit;
  }

  result = GotoReturn_opaque_int32(44);

  exit:
    return result;
}

/**
This function has no early return.
  It tests that fline-comments leaves top-level comments unchanged.
*/
int32_t GotoReturn_no_early_return(int32_t x)
{
  return x;
}

int32_t GotoReturn_early_return_two_args(int32_t x, int32_t y)
{
  int32_t result = 0;

  if (x == 0)
  {
    result = GotoReturn_opaque_int32(42);
    goto exit;
  }

  result = y;

  exit:
    return result;
}

int32_t GotoReturn_collision_test(int32_t x)
{
  int32_t result0 = 0;
  int32_t result = x;

  if (result == 0)
  {
    result0 = GotoReturn_opaque_int32(42);
    goto exit;
  }

  if (result == 1)
  {
    result0 = GotoReturn_opaque_int32(43);
    goto exit;
  }

  result0 = GotoReturn_opaque_int32(44);

  exit:
    return result0;
}

bool GotoReturn_early_return_bool(int32_t x)
{
  bool result = false;

  if (x == 0)
  {
    result = GotoReturn_opaque_bool(true);
    goto exit;
  }

  if (x == 1)
  {
    result = GotoReturn_opaque_bool(false);
    goto exit;
  }

  result = GotoReturn_opaque_bool(true);

  exit:
    return result;
}

uint32_t GotoReturn_early_return_uint32(uint32_t x)
{
  uint32_t result = 0U;

  if (x == 0U)
  {
    result = GotoReturn_opaque_uint32(42U);
    goto exit;
  }

  if (x == 1U)
  {
    result = GotoReturn_opaque_uint32(43U);
    goto exit;
  }

  result = GotoReturn_opaque_uint32(44U);

  exit:
    return result;
}

uint64_t GotoReturn_early_return_uint64(uint64_t x)
{
  uint64_t result = 0ULL;

  if (x == 0ULL)
  {
    result = GotoReturn_opaque_uint64(42ULL);
    goto exit;
  }

  if (x == 1ULL)
  {
    result = GotoReturn_opaque_uint64(43ULL);
    goto exit;
  }

  result = GotoReturn_opaque_uint64(44ULL);

  exit:
    return result;
}

int64_t GotoReturn_early_return_int64(int64_t x)
{
  int64_t result = 0LL;

  if (x == 0LL)
  {
    result = GotoReturn_opaque_int64(42LL);
    goto exit;
  }

  if (x == 1LL)
  {
    result = GotoReturn_opaque_int64(43LL);
    goto exit;
  }

  result = GotoReturn_opaque_int64(44LL);

  exit:
    return result;
}

void GotoReturn_early_return_void(int32_t x)
{
  if (x == 0)
  {
    GotoReturn_side_effect(1);
    goto exit;
  }

  if (x == 1)
  {
    GotoReturn_side_effect(2);
    goto exit;
  }

  GotoReturn_side_effect(3);

  exit:
    return;
}

GotoReturn_point GotoReturn_early_return_struct(int32_t x)
{
  GotoReturn_point result = { 0U };

  if (x == 0)
  {
    result =
      ((GotoReturn_point){ .px = GotoReturn_opaque_int32(1), .py = GotoReturn_opaque_int32(2) });
    goto exit;
  }

  if (x == 1)
  {
    result =
      ((GotoReturn_point){ .px = GotoReturn_opaque_int32(3), .py = GotoReturn_opaque_int32(4) });
    goto exit;
  }

  result =
    ((GotoReturn_point){ .px = GotoReturn_opaque_int32(5), .py = GotoReturn_opaque_int32(6) });

  exit:
    return result;
}

void GotoReturn_unit_return(void)
{

}

int32_t GotoReturn_pulse_early_return(int32_t x)
{
  int32_t _return;
  bool _return1 = false;

  if (x == 0)
  {
    _return = 42;
    _return1 = true;
  }

  bool _return2 = _return1;

  if (!_return2)
    _return = 99;

  return _return;
}

int32_t GotoReturn_main(void)
{
  GotoReturn_early_return_int(0);
  GotoReturn_no_early_return(1);
  GotoReturn_early_return_two_args(0, 1);
  GotoReturn_collision_test(2);
  GotoReturn_early_return_bool(0);
  GotoReturn_early_return_uint32(0U);
  GotoReturn_early_return_uint64(0ULL);
  GotoReturn_early_return_int64(0LL);
  GotoReturn_early_return_void(0);
  GotoReturn_early_return_struct(0);
  GotoReturn_unit_return();
  GotoReturn_pulse_early_return(0);
  return 0;
}

