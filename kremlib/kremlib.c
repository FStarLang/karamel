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
Prims_int FStar_Mul_op_Star(Prims_int x, Prims_int y) { exit(254); }
Prims_int Math_Lib_div(Prims_int x, Prims_int y) { exit(254); }
Prims_int Math_Lib_signed_modulo(Prims_int x, Prims_int y) { exit(254); }
