/* krml header omitted for test repeatability */


#include "SmallIntMacro.h"

#define MAX8 ((uint8_t)~0U)

#define MAX16 ((uint16_t)~0U)

int8_t signed_max8(void)
{
  return (int8_t)((uint32_t)MAX8 >> 1U & 0xFFU);
}

bool equal8(uint8_t x)
{
  return x == MAX8;
}

uint32_t wide8(void)
{
  return (uint32_t)MAX8;
}

uint8_t half8(void)
{
  return (uint32_t)MAX8 / 2U;
}

int16_t signed_max16(void)
{
  return (int16_t)((uint32_t)MAX16 >> 1U & 0xFFFFU);
}

bool equal16(uint16_t x)
{
  return x == MAX16;
}

uint32_t wide16(void)
{
  return (uint32_t)MAX16;
}

uint16_t half16(void)
{
  return (uint32_t)MAX16 / 2U;
}

int32_t main(void)
{
  return 0;
}

