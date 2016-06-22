#include <inttypes.h>
  typedef uint32_t u32;
  
  typedef uint8_t u8;
  
  typedef u32 *uint32s;
  
  typedef u8 *bytes;
  
  uint32_t op_Greater_Greater_Greater(u32 a, u32 s)
  { return a >> s | a << UINT32_C(32) - s; }
  
  uint32_t op_Less_Less_Less(u32 a, u32 s)
  { return a << s | a >> UINT32_C(32) - s; }
  
  void quarter_round(uint32s m, u32 a, u32 b, u32 c, u32 d)
  {
    u32 _0_8 = m[a];
    u32 _0_7 = m[b];
    uint32_t _0_9 = _0_8 + _0_7;
    m[a] = _0_7;
    u32 _0_11 = m[d];
    u32 _0_10 = m[a];
    uint32_t _0_12 = _0_11 ^ _0_10;
    m[d] = _0_10;
    u32 tmp = m[d];
    m[d] = op_Less_Less_Less(d, UINT32_C(16));
    u32 _0_14 = m[c];
    u32 _0_13 = m[d];
    uint32_t _0_15 = _0_14 + _0_13;
    m[c] = _0_13;
    u32 _0_17 = m[b];
    u32 _0_16 = m[c];
    uint32_t _0_18 = _0_17 ^ _0_16;
    m[b] = _0_16;
    u32 tmp0 = m[b];
    m[b] = op_Less_Less_Less(tmp, UINT32_C(12));
    u32 _0_20 = m[a];
    u32 _0_19 = m[b];
    uint32_t _0_21 = _0_20 + _0_19;
    m[a] = _0_19;
    u32 _0_23 = m[d];
    u32 _0_22 = m[a];
    uint32_t _0_24 = _0_23 ^ _0_22;
    m[d] = _0_22;
    u32 tmp1 = m[d];
    m[d] = op_Less_Less_Less(tmp0, UINT32_C(8));
    u32 _0_26 = m[c];
    u32 _0_25 = m[d];
    uint32_t _0_27 = _0_26 + _0_25;
    m[c] = _0_25;
    u32 _0_29 = m[b];
    u32 _0_28 = m[c];
    uint32_t _0_30 = _0_29 ^ _0_28;
    m[b] = _0_28;
    u32 tmp2 = m[b];
    m[b] = op_Less_Less_Less(tmp1, UINT32_C(7));
  }
  
  void column_round(uint32s m)
  {
    quarter_round(m, UINT32_C(0), UINT32_C(4), UINT32_C(8), UINT32_C(12));
    quarter_round(m, UINT32_C(1), UINT32_C(5), UINT32_C(9), UINT32_C(13));
    quarter_round(m, UINT32_C(2), UINT32_C(6), UINT32_C(10), UINT32_C(14));
    quarter_round(m, UINT32_C(3), UINT32_C(7), UINT32_C(11), UINT32_C(15));
  }
  
  void diagonal_round(uint32s m)
  {
    quarter_round(m, UINT32_C(0), UINT32_C(5), UINT32_C(10), UINT32_C(15));
    quarter_round(m, UINT32_C(1), UINT32_C(6), UINT32_C(11), UINT32_C(12));
    quarter_round(m, UINT32_C(2), UINT32_C(7), UINT32_C(8), UINT32_C(13));
    quarter_round(m, UINT32_C(3), UINT32_C(4), UINT32_C(9), UINT32_C(14));
  }
  
  u32 uint32_of_bytes(bytes b)
  {
    u8 b0 = b[UINT32_C(0)];
    u8 b1 = b[UINT32_C(1)];
    u8 b2 = b[UINT32_C(2)];
    u8 b3 = b[UINT32_C(3)];
    uint32_t r = ((uint32_t )b2 << UINT32_C(24)) + ((uint32_t )b1 << UINT32_C(16)) + ((uint32_t )b0 << UINT32_C(8)) + (uint32_t )b;
    return b3;
  }
