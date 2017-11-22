#ifndef __KREMLIN_CHECKEDINTS_H
#define __KREMLIN_CHECKEDINTS_H

/******************************************************************************/
/* Checked integers to ease the compilation of non-Low* code                  */
/******************************************************************************/

typedef int32_t Prims_pos, Prims_nat, Prims_nonzero, Prims_int,
    krml_checked_int_t;

inline static bool Prims_op_GreaterThanOrEqual(int32_t x, int32_t y) {
  return x >= y;
}

inline static bool Prims_op_LessThanOrEqual(int32_t x, int32_t y) {
  return x <= y;
}

inline static bool Prims_op_GreaterThan(int32_t x, int32_t y) { return x > y; }

inline static bool Prims_op_LessThan(int32_t x, int32_t y) { return x < y; }

#define RETURN_OR(x)                                                           \
  do {                                                                         \
    int64_t __ret = x;                                                         \
    if (__ret < INT32_MIN || INT32_MAX < __ret) {                              \
      KRML_HOST_PRINTF("Prims.{int,nat,pos} integer overflow at %s:%d\n",      \
                       __FILE__, __LINE__);                                    \
      KRML_HOST_EXIT(252);                                                     \
    }                                                                          \
    return (int32_t)__ret;                                                     \
  } while (0)

inline static int32_t Prims_pow2(int32_t x) {
  RETURN_OR((int64_t)1 << (int64_t)x);
}

inline static int32_t Prims_op_Multiply(int32_t x, int32_t y) {
  RETURN_OR((int64_t)x * (int64_t)y);
}

inline static int32_t Prims_op_Addition(int32_t x, int32_t y) {
  RETURN_OR((int64_t)x + (int64_t)y);
}

inline static int32_t Prims_op_Subtraction(int32_t x, int32_t y) {
  RETURN_OR((int64_t)x - (int64_t)y);
}

inline static int32_t Prims_op_Division(int32_t x, int32_t y) {
  RETURN_OR((int64_t)x / (int64_t)y);
}

inline static int32_t Prims_op_Modulus(int32_t x, int32_t y) {
  RETURN_OR((int64_t)x % (int64_t)y);
}

inline static int8_t FStar_UInt8_uint_to_t(int8_t x) { return x; }
inline static int16_t FStar_UInt16_uint_to_t(int16_t x) { return x; }
inline static int32_t FStar_UInt32_uint_to_t(int32_t x) { return x; }
inline static int64_t FStar_UInt64_uint_to_t(int64_t x) { return x; }

inline static int8_t FStar_UInt8_v(int8_t x) { return x; }
inline static int16_t FStar_UInt16_v(int16_t x) { return x; }
inline static int32_t FStar_UInt32_v(int32_t x) { return x; }
inline static int64_t FStar_UInt64_v(int64_t x) { return x; }

#end
