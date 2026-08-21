/* krml header omitted for test repeatability */


#include "IntCmpFold.h"

void IntCmpFold_main(void)
{
  IntCmpFold_f(false);
  IntCmpFold_f(true);
  IntCmpFold_f(true);
  IntCmpFold_f(false);
  IntCmpFold_f(false);
  IntCmpFold_f(true);
  IntCmpFold_f(true);
  IntCmpFold_f(false);
  IntCmpFold_f(true);
}

void IntCmpFold_main_signed(void)
{
  IntCmpFold_f(false);
  IntCmpFold_f(true);
  IntCmpFold_f(true);
  IntCmpFold_f(false);
  IntCmpFold_f(false);
  IntCmpFold_f(true);
  IntCmpFold_f(true);
  IntCmpFold_f(false);
  IntCmpFold_f(true);
}

void IntCmpFold_main_uint8(void)
{
  IntCmpFold_f(true);
  IntCmpFold_f(false);
}

void IntCmpFold_main_int8(void)
{
  IntCmpFold_f(true);
  IntCmpFold_f(false);
}

void IntCmpFold_main_uint16(void)
{
  IntCmpFold_f(true);
  IntCmpFold_f(false);
}

void IntCmpFold_main_int16(void)
{
  IntCmpFold_f(true);
  IntCmpFold_f(false);
}

void IntCmpFold_main_uint64(void)
{
  IntCmpFold_f(true);
  IntCmpFold_f(false);
}

void IntCmpFold_main_int64(void)
{
  IntCmpFold_f(true);
  IntCmpFold_f(false);
}

void IntCmpFold_main_sizet(void)
{
  IntCmpFold_f(true);
  IntCmpFold_f(false);
}

void IntCmpFold_main_var(uint32_t z)
{
  IntCmpFold_f(1U == z);
  IntCmpFold_f(z < 1U);
}

void IntCmpFold_main_var_signed(int32_t z)
{
  IntCmpFold_f(-1 == z);
  IntCmpFold_f(z < -1);
}

void IntCmpFold_main_var_narrow(uint8_t z)
{
  IntCmpFold_f(255U == z);
  IntCmpFold_f(z < 255U);
}

void IntCmpFold_cast_prevents_fold(void)
{
  IntCmpFold_f((uint16_t)1U < 2U);
}

