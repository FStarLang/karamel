/* krml header omitted for test repeatability */


#include "DanglingElse.h"

uint32_t choose(bool a, bool b, bool c, uint32_t *p)
{
  if (a)
  {
    if (b)
      p[0U] = 1U;
    else if (c)
      p[0U] = 2U;
  }
  else
    p[0U] = 3U;
  return p[0U];
}

bool test_case(bool a, bool b, bool c, uint32_t expected)
{
  uint32_t p = 9U;
  uint32_t got = choose(a, b, c, &p);
  uint32_t cell = p;
  return got == expected && cell == expected;
}

int32_t main(void)
{
  bool fff = test_case(false, false, false, 3U);
  bool fft = test_case(false, false, true, 3U);
  bool ftf = test_case(false, true, false, 3U);
  bool ftt = test_case(false, true, true, 3U);
  bool tff = test_case(true, false, false, 9U);
  bool tft = test_case(true, false, true, 2U);
  bool ttf = test_case(true, true, false, 1U);
  bool ttt = test_case(true, true, true, 1U);
  return fff && fft && ftf && ftt && tff && tft && ttf && ttt ? 0 : 1;
}

