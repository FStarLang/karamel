#include <inttypes.h>
#include <string.h>
#include "include/krml/internal/target.h"

void test(uint32_t *st, uint32_t y, uint32_t z) {
  uint32_t x = y + z;

  int num = 0;
  int sum = 0;

  // for loop terminates when count exceeds num
  for(int count = 1; count < num; count++)
  {
      sum += count;
  }
}


void quarter_round(uint32_t *st, uint32_t a, uint32_t b, uint32_t c, uint32_t d)
{
  uint32_t sta = st[a];
  uint32_t stb0 = st[b];
  uint32_t std0 = st[d];
  uint32_t sta10 = sta + stb0;
  uint32_t std10 = std0 ^ sta10;
  uint32_t std2 = std10 << 16U | std10 >> 16U;
  st[a] = sta10;
  st[d] = std2;
  uint32_t sta0 = st[c];
  uint32_t stb1 = st[d];
  uint32_t std3 = st[b];
  uint32_t sta11 = sta0 + stb1;
  uint32_t std11 = std3 ^ sta11;
  uint32_t std20 = std11 << 12U | std11 >> 20U;
  st[c] = sta11;
  st[b] = std20;
  uint32_t sta2 = st[a];
  uint32_t stb2 = st[b];
  uint32_t std4 = st[d];
  uint32_t sta12 = sta2 + stb2;
  uint32_t std12 = std4 ^ sta12;
  uint32_t std21 = std12 << 8U | std12 >> 24U;
  st[a] = sta12;
  st[d] = std21;
  uint32_t sta3 = st[c];
  uint32_t stb = st[d];
  uint32_t std = st[b];
  uint32_t sta1 = sta3 + stb;
  uint32_t std1 = std ^ sta1;
  uint32_t std22 = std1 << 7U | std1 >> 25U;
  st[c] = sta1;
  st[b] = std22;
}

static inline void double_round(uint32_t *st)
{
  quarter_round(st, 0U, 4U, 8U, 12U);
  quarter_round(st, 1U, 5U, 9U, 13U);
  quarter_round(st, 2U, 6U, 10U, 14U);
  quarter_round(st, 3U, 7U, 11U, 15U);
  quarter_round(st, 0U, 5U, 10U, 15U);
  quarter_round(st, 1U, 6U, 11U, 12U);
  quarter_round(st, 2U, 7U, 8U, 13U);
  quarter_round(st, 3U, 4U, 9U, 14U);
}

static inline void rounds(uint32_t *st)
{
  double_round(st);
  double_round(st);
  double_round(st);
  double_round(st);
  double_round(st);
  double_round(st);
  double_round(st);
  double_round(st);
  double_round(st);
  double_round(st);
}

// static inline void chacha20_core(uint32_t *k, uint32_t *ctx, uint32_t ctr)
// {
//   memcpy(k, ctx, 16U * sizeof (uint32_t));
//   uint32_t ctr_u32 = ctr;
//   k[12U] = k[12U] + ctr_u32;
//   rounds(k);
//   KRML_MAYBE_FOR16(i,
//     0U,
//     32U,
//     1U,
//     uint32_t x = k[i] + ctx[i];
//     uint32_t *os = k;
//     os[i] = x;);
//   k[12U] = k[12U] + ctr_u32;
// }
