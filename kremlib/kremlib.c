#include <stdlib.h>
#include "kremlib.h"

int exit_success = EXIT_SUCCESS;
int exit_failure = EXIT_FAILURE;


/* Constant time comparisons */
uint8_t FStar_UInt8_eq_mask(uint8_t x, uint8_t y) {
  x = ~(x ^ y);
  x &= x << 4;
  x &= x << 2;
  x &= x << 1;
  return (int8_t)x >> 7;
}
uint8_t FStar_UInt8_gte_mask(uint8_t x, uint8_t y) {
  return ~(uint8_t)(((int32_t)x - y) >> 31);
}

uint32_t FStar_UInt32_eq_mask(uint32_t x, uint32_t y) {
  x = ~(x ^ y);
  x &= x << 16;
  x &= x << 8;
  x &= x << 4;
  x &= x << 2;
  x &= x << 1;
  return ((int32_t)x) >> 31;
}
uint32_t FStar_UInt32_gte_mask(uint32_t x, uint32_t y) {
  return ~((uint32_t)(((int64_t)x - y) >> 63));
}

uint64_t FStar_UInt64_eq_mask(uint64_t x, uint64_t y) {
  x = ~(x ^ y);
  x &= x << 32;
  x &= x << 16;
  x &= x << 8;
  x &= x << 4;
  x &= x << 2;
  x &= x << 1;
  return ((int64_t)x) >> 63;
}
uint64_t FStar_UInt64_gte_mask(uint64_t x, uint64_t y) {
  uint64_t low63 = ~((uint64_t)((int64_t)((int64_t)(x & UINT64_C(0x7fffffffffffffff))
                                          - (int64_t)(y & UINT64_C(0x7fffffffffffffff))) >> 63));
  uint64_t high_bit = ~((uint64_t)((int64_t)((int64_t)(x & UINT64_C(0x8000000000000000))
                                             - (int64_t)(y & UINT64_C(0x8000000000000000))) >> 63));
  return low63 & high_bit;
}

#ifdef __GNUC__
FStar_UInt128_t FStar_UInt128_add(FStar_UInt128_t x, FStar_UInt128_t y){
  return x + y;
}

FStar_UInt128_t FStar_UInt128_add_mod(FStar_UInt128_t x, FStar_UInt128_t y){
  return x + y;
}

FStar_UInt128_t FStar_UInt128_sub(FStar_UInt128_t x, FStar_UInt128_t y){
  return x - y;
}

FStar_UInt128_t FStar_UInt128_sub_mod(FStar_UInt128_t x, FStar_UInt128_t y){
  return x - y;
}

FStar_UInt128_t FStar_UInt128_logand(FStar_UInt128_t x, FStar_UInt128_t y){
  return x & y;
}

FStar_UInt128_t FStar_UInt128_logor(FStar_UInt128_t x, FStar_UInt128_t y){
  return x | y;
}

FStar_UInt128_t FStar_UInt128_logxor(FStar_UInt128_t x, FStar_UInt128_t y){
  return x ^ y;
}

FStar_UInt128_t FStar_UInt128_lognot(FStar_UInt128_t x){
  return ~x;
}

/* y >= 128 should never happen */
FStar_UInt128_t FStar_UInt128_shift_left(FStar_UInt128_t x, FStar_UInt32_t y){
  return x << y;
}

FStar_UInt128_t FStar_UInt128_shift_right(FStar_UInt128_t x, FStar_UInt32_t y){
  return x >> y;
}

/* Conversions */
FStar_UInt128_t FStar_Int_Cast_uint64_to_uint128(uint64_t x){
  return (FStar_UInt128_t)x;
}

uint64_t FStar_Int_Cast_uint128_to_uint64(FStar_UInt128_t x){
  return (uint64_t)x;
}

FStar_UInt128_t FStar_UInt128_eq_mask(FStar_UInt128_t x, FStar_UInt128_t y){
  uint64_t mask = FStar_UInt64_eq_mask((uint64_t)(x >> 64), (uint64_t)(y >> 64))
    & FStar_UInt64_eq_mask(x, y);
  return ((FStar_UInt128_t)mask) << 64 | mask;
}

FStar_UInt128_t FStar_UInt128_gte_mask(FStar_UInt128_t x, FStar_UInt128_t y){
  uint64_t mask = (FStar_UInt64_gte_mask(x >> 64, y >> 64) & ~(FStar_UInt64_eq_mask(x >> 64, y >> 64)))
    | (FStar_UInt64_eq_mask(x >> 64, y >> 64) & FStar_UInt64_gte_mask(x, y));
  return ((FStar_UInt128_t)mask) << 64 | mask;
}

FStar_UInt128_t FStar_UInt128_mul_wide(uint64_t x, uint64_t y){
  return (FStar_UInt128_t)x * y;
}
#else

/* From OPENSSL's code base */
# define CONSTANT_TIME_CARRY(a,b) (                             \
         (a ^ ((a ^ b) | ((a - b) ^ b))) >> (sizeof(a) * 8 - 1) \
         )

FStar_UInt128_t FStar_UInt128_add(FStar_UInt128_t x, FStar_UInt128_t y){
  FStar_UInt128_t r;
  r.low = x.low + y.low;
  r.high = x.high + y.high + CONSTANT_TIME_CARRY(r.low, y.low);
  return r;
}

FStar_UInt128_t FStar_UInt128_add_mod(FStar_UInt128_t x, FStar_UInt128_t y){
  return FStar_UInt128_add(x, y);
}

FStar_UInt128_t FStar_UInt128_sub(FStar_UInt128_t x, FStar_UInt128_t y){
  FStar_UInt128_t r;
  r.low = x.low - y.low;
  r.high = x.high - y.high  - CONSTANT_TIME_CARRY(x.low, r.low);
  return r;
}

FStar_UInt128_t FStar_UInt128_sub_mod(FStar_UInt128_t x, FStar_UInt128_t y){
  return FStar_UInt128_sub(x, y);
}

FStar_UInt128_t FStar_UInt128_logand(FStar_UInt128_t x, FStar_UInt128_t y){
  FStar_UInt128_t r;
  r.high = x.high & y.high;
  r.low  = x.low & y.low;
  return r;
}

FStar_UInt128_t FStar_UInt128_logor(FStar_UInt128_t x, FStar_UInt128_t y){
  FStar_UInt128_t r;
  r.high = x.high | y.high;
  r.low  = x.low | y.low;
  return r;
}

FStar_UInt128_t FStar_UInt128_logxor(FStar_UInt128_t x, FStar_UInt128_t y){
  FStar_UInt128_t r;
  r.high = x.high ^ y.high;
  r.low  = x.low ^ y.low;
  return r;
}

FStar_UInt128_t FStar_UInt128_lognot(FStar_UInt128_t x){
  FStar_UInt128_t r;
  r.high = ~x.high;
  r.low  = ~x.low;
  return r;
}

/* y >= 128 should never happen */
FStar_UInt128_t FStar_UInt128_shift_left(FStar_UInt128_t x, FStar_UInt32_t y){
  FStar_UInt128_t r;
  uint64_t mask_64_m = (((int64_t)y - 64) >> 63);
  uint64_t mask_64_p = ((64 - (int64_t)y) >> 63);
  uint64_t mask_64   = ~(mask_64_m | mask_64_p);
  uint64_t mask_0    = ((int64_t)y - 1)>>63;
  r.low = mask_64_m & (x.low << y);
  r.high = (mask_64_m & ((x.high << y) | ((~mask_0) & (x.low >> (64 - y)))))
    | ((mask_64_p) & (x.low << (y-64)))
    | (mask_64 & x.low);
  return r;
}

FStar_UInt128_t FStar_UInt128_shift_right(FStar_UInt128_t x, FStar_UInt32_t y){
  FStar_UInt128_t r;
  uint64_t mask_64_m = (((int64_t)y - 64) >> 63);
  uint64_t mask_64_p = ((64 - (int64_t)y) >> 63);
  uint64_t mask_64   = ~(mask_64_m | mask_64_p);
  uint64_t mask_0    = ((int64_t)y - 1)>>63;
  r.high = mask_64_m & (x.high >> y);
  r.low = (mask_64_m & ((x.low >> y) | ((~mask_0) & (x.high << (64 - y)))))
    | ((mask_64_p) & (x.high >> (y-64)))
    | (mask_64 & x.high);
  return r;
}

/* Conversions */
FStar_UInt128_t FStar_Int_Cast_uint64_to_uint128(uint64_t x){
  return (FStar_UInt128_t){.high = UINT64_C(0), .low = x};
}

uint64_t FStar_Int_Cast_uint128_to_uint64(FStar_UInt128_t x){
  return x.low;
}

FStar_UInt128_t FStar_UInt128_eq_mask(FStar_UInt128_t x, FStar_UInt128_t y){
  return (FStar_UInt128_t){.low = FStar_UInt64_eq_mask(x.low, y.low),
      .high = FStar_UInt64_eq_mask(x.high, y.high)};
}

FStar_UInt128_t FStar_UInt128_gte_mask(FStar_UInt128_t x, FStar_UInt128_t y){
  uint64_t mask = (FStar_UInt64_gte_mask(x.high, y.high) & ~(FStar_UInt64_eq_mask(x.high, y.high)))
    | (FStar_UInt64_eq_mask(x.high, y.high) & FStar_UInt64_gte_mask(x.low, y.low));
  return (FStar_UInt128_t){.high = mask, .low = mask};
}

FStar_UInt128_t FStar_UInt128_mul_wide(uint64_t x, uint64_t y){
  uint64_t u1, v1, t, w3, k, w1;
  u1 = (x & 0xffffffff);
  v1 = (y & 0xffffffff);
  t = (u1 * v1);
  w3 = (t & 0xffffffff);
  k = (t >> 32);
  x >>= 32;
  t = (x * v1) + k;
  k = (t & 0xffffffff);
  w1 = (t >> 32);
  y >>= 32;
  t = (u1 * y) + k;
  k = (t >> 32);
  return (FStar_UInt128_t){.high = (x * y) + w1 + k, .low = (t << 32) + w3};
}
#endif

bool FStar_UInt128_op_Greater_Greater_Hat(FStar_UInt128_t x, FStar_UInt32_t y) {
#ifdef __GNUC__
  return x >> y;
#else
  exit(254);
#endif
}

bool Prims_op_GreaterThanOrEqual(Prims_int x, Prims_int y) { exit(254); }
bool Prims_op_LessThanOrEqual(Prims_int x, Prims_int y) { exit(254); }
bool Prims_op_GreaterThan(Prims_int x, Prims_int y) { exit(254); }
bool Prims_op_LessThan(Prims_int x, Prims_int y) { exit(254); }
Prims_int Prims_pow2(Prims_int x) { exit(254); }
Prims_int Prims_op_Multiply(Prims_int x, Prims_int y) { exit(254); }
Prims_int Prims_op_Addition(Prims_int x, Prims_int y) { exit(254); }
Prims_int Prims_op_Subtraction(Prims_int x, Prims_int y) { exit(254); }
Prims_int Prims_op_Division(Prims_int x, Prims_int y) { exit(254); }
Prims_int Prims_op_Modulus(Prims_int x, Prims_int y) { exit(254); }
void *Prims_magic(void *_) { exit(254); }
void *Prims____Cons___tl(void *_) { exit(254); }

Prims_int FStar_UInt32_v(uint32_t x) { exit(254); }
FStar_Seq_seq FStar_Seq_createEmpty(void *_) { exit(254); }
FStar_Seq_seq FStar_Seq_create(Prims_nat len, void *init) { exit(254); }
FStar_Seq_seq FStar_Seq_upd(FStar_Seq_seq s, Prims_nat index, void *elt) { exit(254); }
FStar_Seq_seq FStar_Seq_append(FStar_Seq_seq x, FStar_Seq_seq y) { exit(254); }
FStar_Seq_seq FStar_SeqProperties_snoc(FStar_Seq_seq x, Prims_nat y) { exit(254); }
FStar_Seq_seq FStar_SeqProperties_cons(int x, FStar_Seq_seq y) { exit(254); }
int FStar_Seq_index(FStar_Seq_seq x, Prims_int y) { exit(254); }
