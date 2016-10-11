#include "kremlib.h"
#include <stdlib.h>

int exit_success = EXIT_SUCCESS;
int exit_failure = EXIT_FAILURE;

// Constant time comparisons
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
  uint64_t low63 =
      ~((uint64_t)((int64_t)((int64_t)(x & UINT64_C(0x7fffffffffffffff)) -
                             (int64_t)(y & UINT64_C(0x7fffffffffffffff))) >>
                   63));
  uint64_t high_bit =
      ~((uint64_t)((int64_t)((int64_t)(x & UINT64_C(0x8000000000000000)) -
                             (int64_t)(y & UINT64_C(0x8000000000000000))) >>
                   63));
  return low63 & high_bit;
}

// 128-bit arithmetic
#ifdef __GNUC__
#include "native128.c"
#else
#include "custom128.c"
#endif

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
FStar_Seq_seq FStar_Seq_upd(FStar_Seq_seq s, Prims_nat index, void *elt) {
  exit(254);
}
FStar_Seq_seq FStar_Seq_append(FStar_Seq_seq x, FStar_Seq_seq y) { exit(254); }
FStar_Seq_seq FStar_SeqProperties_snoc(FStar_Seq_seq x, Prims_nat y) {
  exit(254);
}
FStar_Seq_seq FStar_SeqProperties_cons(int x, FStar_Seq_seq y) { exit(254); }
int FStar_Seq_index(FStar_Seq_seq x, Prims_int y) { exit(254); }
