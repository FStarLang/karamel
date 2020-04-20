/*
  Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
  Licensed under the Apache 2.0 License.
*/

#include <inttypes.h>
#include "kremlib.h"
#include "kremlin/internal/compat.h"
#include "kremlin/internal/target.h"

#ifndef __FStar_Int_H
#define __FStar_Int_H

#include "FStar_BitVector.h"


extern Prims_int FStar_Int_max_int(Prims_pos n);

extern Prims_int FStar_Int_min_int(Prims_pos n);

extern bool FStar_Int_fits(Prims_int x, Prims_pos n);

extern Prims_int FStar_Int_op_Slash(Prims_int a, Prims_int b);

extern Prims_int FStar_Int_op_At_Percent(Prims_int v, Prims_int p);

extern Prims_int FStar_Int_zero(Prims_pos n);

extern Prims_int FStar_Int_pow2_n(Prims_pos n, Prims_int p);

extern Prims_int FStar_Int_pow2_minus_one(Prims_pos n, Prims_int m);

extern Prims_int FStar_Int_one(Prims_pos n);

extern Prims_int FStar_Int_ones(Prims_pos n);

extern Prims_int FStar_Int_incr(Prims_pos n, Prims_int a);

extern Prims_int FStar_Int_decr(Prims_pos n, Prims_int a);

extern Prims_int FStar_Int_incr_underspec(Prims_pos n, Prims_int a);

extern Prims_int FStar_Int_decr_underspec(Prims_pos n, Prims_int a);

extern Prims_int FStar_Int_incr_mod(Prims_pos n, Prims_int a);

extern Prims_int FStar_Int_decr_mod(Prims_pos n, Prims_int a);

extern Prims_int FStar_Int_add(Prims_pos n, Prims_int a, Prims_int b);

extern Prims_int FStar_Int_add_underspec(Prims_pos n, Prims_int a, Prims_int b);

extern Prims_int FStar_Int_add_mod(Prims_pos n, Prims_int a, Prims_int b);

extern Prims_int FStar_Int_sub(Prims_pos n, Prims_int a, Prims_int b);

extern Prims_int FStar_Int_sub_underspec(Prims_pos n, Prims_int a, Prims_int b);

extern Prims_int FStar_Int_sub_mod(Prims_pos n, Prims_int a, Prims_int b);

extern Prims_int FStar_Int_mul(Prims_pos n, Prims_int a, Prims_int b);

extern Prims_int FStar_Int_mul_underspec(Prims_pos n, Prims_int a, Prims_int b);

extern Prims_int FStar_Int_mul_mod(Prims_pos n, Prims_int a, Prims_int b);

extern Prims_int FStar_Int_div(Prims_pos n, Prims_int a, Prims_int b);

extern Prims_int FStar_Int_div_underspec(Prims_pos n, Prims_int a, Prims_int b);

extern Prims_int FStar_Int_udiv(Prims_pos n, Prims_int a, Prims_int b);

extern Prims_int FStar_Int_mod_(Prims_pos n, Prims_int a, Prims_int b);

extern bool FStar_Int_eq(Prims_pos n, Prims_int a, Prims_int b);

extern bool FStar_Int_gt(Prims_pos n, Prims_int a, Prims_int b);

extern bool FStar_Int_gte(Prims_pos n, Prims_int a, Prims_int b);

extern bool FStar_Int_lt(Prims_pos n, Prims_int a, Prims_int b);

extern bool FStar_Int_lte(Prims_pos n, Prims_int a, Prims_int b);

extern Prims_int FStar_Int_to_uint(Prims_pos n, Prims_int x);

extern Prims_int FStar_Int_from_uint(Prims_pos n, Prims_int x);

extern Prims_int FStar_Int_to_int_t(Prims_pos m, Prims_int a);

extern Prims_list__bool *FStar_Int_to_vec(Prims_pos n, Prims_int num);

extern Prims_int FStar_Int_from_vec(Prims_pos n, Prims_list__bool *vec);

extern bool FStar_Int_nth(Prims_pos n, Prims_int a, Prims_int i);

extern Prims_int FStar_Int_logand(Prims_pos n, Prims_int a, Prims_int b);

extern Prims_int FStar_Int_logxor(Prims_pos n, Prims_int a, Prims_int b);

extern Prims_int FStar_Int_logor(Prims_pos n, Prims_int a, Prims_int b);

extern Prims_int FStar_Int_lognot(Prims_pos n, Prims_int a);

extern Prims_int FStar_Int_minus(Prims_pos n, Prims_int a);

extern Prims_int FStar_Int_shift_left(Prims_pos n, Prims_int a, Prims_int s);

extern Prims_int FStar_Int_shift_right(Prims_pos n, Prims_int a, Prims_int s);

extern Prims_int FStar_Int_shift_arithmetic_right(Prims_pos n, Prims_int a, Prims_int s);

#define __FStar_Int_H_DEFINED
#endif
