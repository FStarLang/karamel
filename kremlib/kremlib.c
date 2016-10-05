#include <stdlib.h>
#include "kremlib.h"

int exit_success = EXIT_SUCCESS;
int exit_failure = EXIT_FAILURE;

uint64_t FStar_UInt64_gte_mask(uint64_t x, uint64_t y) {
  return x >= y ? UINT64_C(0xffffffffffffffff) : 0;
}

uint64_t FStar_UInt64_eq_mask(uint64_t x, uint64_t y) {
  return x == y ? UINT64_C(0xffffffffffffffff) : 0;
}

uint8_t FStar_UInt8_eq_mask(uint8_t x, uint8_t y) {
  return x == y ? UINT8_C(0xff) : 0;
}

bool FStar_UInt128_op_Greater_Greater_Hat(FStar_UInt128_t x, FStar_UInt32_t y) {
  return x >> y;
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
Prims_int FStar_Int_op_At_Percent(Prims_int x, Prims_int y) { exit(254); }
FStar_Seq_seq FStar_Seq_createEmpty(void *_) { exit(254); }
FStar_Seq_seq FStar_SeqProperties_snoc(FStar_Seq_seq x, Prims_nat y) { exit(254); }
FStar_Seq_seq FStar_SeqProperties_cons(int x, FStar_Seq_seq y) { exit(254); }
int FStar_Seq_index(FStar_Seq_seq x, Prims_int y) { exit(254); }
