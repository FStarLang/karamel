/* krml header omitted for test repeatability */


#include "Floats.h"

float Floats_neg32(float x)
{
  return (float)0LL - x;
}

double Floats_neg64(double x)
{
  return (double)0LL - x;
}

float Floats_float_array(void)
{
  float a[16U];
  memset(a, 0U, (size_t)16U * sizeof (float));
  return a[0U];
}

