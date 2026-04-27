/* krml header omitted for test repeatability */


#include "GotoReturn.h"

int32_t GotoReturn_early_return_int(int32_t x)
{
  int32_t result = (int32_t)0;
  if (x == (int32_t)0)
  {
    result = (int32_t)42;
    goto exit;
  }
  if (x == (int32_t)1)
  {
    result = (int32_t)43;
    goto exit;
  }
  result = (int32_t)44;
  exit:
    return result;
}

int32_t GotoReturn_no_early_return(int32_t x)
{
  return x;
}

int32_t GotoReturn_early_return_two_args(int32_t x, int32_t y)
{
  int32_t result = (int32_t)0;
  if (x == (int32_t)0)
  {
    result = (int32_t)42;
    goto exit;
  }
  result = y;
  exit:
    return result;
}

int32_t GotoReturn_collision_test(int32_t x)
{
  int32_t result0 = (int32_t)0;
  int32_t result = x;
  if (result == (int32_t)0)
  {
    result0 = (int32_t)42;
    goto exit;
  }
  if (result == (int32_t)1)
  {
    result0 = (int32_t)43;
    goto exit;
  }
  result0 = (int32_t)44;
  exit:
    return result0;
}

bool GotoReturn_early_return_bool(int32_t x)
{
  bool result = false;
  if (x == (int32_t)0)
  {
    result = true;
    goto exit;
  }
  if (x == (int32_t)1)
  {
    result = false;
    goto exit;
  }
  result = true;
  exit:
    return result;
}

uint32_t GotoReturn_early_return_uint32(uint32_t x)
{
  uint32_t result = 0U;
  if (x == 0U)
  {
    result = 42U;
    goto exit;
  }
  if (x == 1U)
  {
    result = 43U;
    goto exit;
  }
  result = 44U;
  exit:
    return result;
}

uint64_t GotoReturn_early_return_uint64(uint64_t x)
{
  uint64_t result = 0ULL;
  if (x == 0ULL)
  {
    result = 42ULL;
    goto exit;
  }
  if (x == 1ULL)
  {
    result = 43ULL;
    goto exit;
  }
  result = 44ULL;
  exit:
    return result;
}

int64_t GotoReturn_early_return_int64(int64_t x)
{
  int64_t result = (int64_t)0LL;
  if (x == (int64_t)0LL)
  {
    result = (int64_t)42LL;
    goto exit;
  }
  if (x == (int64_t)1LL)
  {
    result = (int64_t)43LL;
    goto exit;
  }
  result = (int64_t)44LL;
  exit:
    return result;
}

void GotoReturn_early_return_void(int32_t x)
{
  if (x == (int32_t)0)
  {
    GotoReturn_side_effect((int32_t)1);
    goto exit;
  }
  if (x == (int32_t)1)
  {
    GotoReturn_side_effect((int32_t)2);
    goto exit;
  }
  GotoReturn_side_effect((int32_t)3);
  exit:
    return;
}

GotoReturn_point GotoReturn_early_return_struct(int32_t x)
{
  GotoReturn_point result = { 0U };
  if (x == (int32_t)0)
  {
    result = ((GotoReturn_point){ .px = (int32_t)1, .py = (int32_t)2 });
    goto exit;
  }
  if (x == (int32_t)1)
  {
    result = ((GotoReturn_point){ .px = (int32_t)3, .py = (int32_t)4 });
    goto exit;
  }
  result = ((GotoReturn_point){ .px = (int32_t)5, .py = (int32_t)6 });
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
  if (x == (int32_t)0)
  {
    _return = (int32_t)42;
    _return1 = true;
  }
  bool _return2 = _return1;
  if (!_return2)
    _return = (int32_t)99;
  return _return;
}

int32_t GotoReturn_main(void)
{
  GotoReturn_early_return_int((int32_t)0);
  GotoReturn_no_early_return((int32_t)1);
  GotoReturn_early_return_two_args((int32_t)0, (int32_t)1);
  GotoReturn_collision_test((int32_t)2);
  GotoReturn_early_return_bool((int32_t)0);
  GotoReturn_early_return_uint32(0U);
  GotoReturn_early_return_uint64(0ULL);
  GotoReturn_early_return_int64((int64_t)0LL);
  GotoReturn_early_return_void((int32_t)0);
  GotoReturn_early_return_struct((int32_t)0);
  GotoReturn_unit_return();
  GotoReturn_pulse_early_return((int32_t)0);
  return (int32_t)0;
}

