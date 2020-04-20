/*
  Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
  Licensed under the Apache 2.0 License.
*/

#include <inttypes.h>
#include "kremlib.h"
#include "kremlin/internal/compat.h"
#include "kremlin/internal/target.h"

#ifndef __FStar_UInt_H
#define __FStar_UInt_H

#include "FStar_BitVector.h"


extern Prims_int FStar_UInt_max_int(Prims_int n);

extern Prims_int FStar_UInt_min_int(Prims_int n);

extern bool FStar_UInt_fits(Prims_int x, Prims_int n);

extern Prims_int FStar_UInt_zero(Prims_int n);

extern Prims_int FStar_UInt_pow2_n(Prims_pos n, Prims_int p);

extern Prims_int FStar_UInt_one(Prims_pos n);

extern Prims_int FStar_UInt_ones(Prims_int n);

extern Prims_int FStar_UInt_incr(Prims_int n, Prims_int a);

extern Prims_int FStar_UInt_decr(Prims_int n, Prims_int a);

extern Prims_int FStar_UInt_incr_underspec(Prims_int n, Prims_int a);

extern Prims_int FStar_UInt_decr_underspec(Prims_int n, Prims_int a);

extern Prims_int FStar_UInt_incr_mod(Prims_int n, Prims_int a);

extern Prims_int FStar_UInt_decr_mod(Prims_int n, Prims_int a);

extern Prims_int FStar_UInt_add(Prims_int n, Prims_int a, Prims_int b);

extern Prims_int FStar_UInt_add_underspec(Prims_int n, Prims_int a, Prims_int b);

extern Prims_int FStar_UInt_add_mod(Prims_int n, Prims_int a, Prims_int b);

extern Prims_int FStar_UInt_sub(Prims_int n, Prims_int a, Prims_int b);

extern Prims_int FStar_UInt_sub_underspec(Prims_int n, Prims_int a, Prims_int b);

extern Prims_int FStar_UInt_sub_mod(Prims_int n, Prims_int a, Prims_int b);

extern Prims_int FStar_UInt_mul(Prims_int n, Prims_int a, Prims_int b);

extern Prims_int FStar_UInt_mul_underspec(Prims_int n, Prims_int a, Prims_int b);

extern Prims_int FStar_UInt_mul_mod(Prims_int n, Prims_int a, Prims_int b);

extern Prims_int FStar_UInt_mul_div(Prims_int n, Prims_int a, Prims_int b);

extern Prims_int FStar_UInt_div(Prims_int n, Prims_int a, Prims_int b);

extern Prims_int FStar_UInt_div_underspec(Prims_int n, Prims_int a, Prims_int b);

extern Prims_int FStar_UInt_udiv(Prims_pos n, Prims_int a, Prims_int b);

extern Prims_int FStar_UInt_mod_(Prims_int n, Prims_int a, Prims_int b);

extern bool FStar_UInt_eq(Prims_int n, Prims_int a, Prims_int b);

extern bool FStar_UInt_gt(Prims_int n, Prims_int a, Prims_int b);

extern bool FStar_UInt_gte(Prims_int n, Prims_int a, Prims_int b);

extern bool FStar_UInt_lt(Prims_int n, Prims_int a, Prims_int b);

extern bool FStar_UInt_lte(Prims_int n, Prims_int a, Prims_int b);

extern Prims_int FStar_UInt_to_uint_t(Prims_int m, Prims_int a);

extern Prims_list__bool *FStar_UInt_to_vec(Prims_int n, Prims_int num);

extern Prims_int FStar_UInt_from_vec(Prims_int n, Prims_list__bool *vec);

extern bool FStar_UInt_nth(Prims_pos n, Prims_int a, Prims_int i);

extern Prims_int FStar_UInt_logand(Prims_pos n, Prims_int a, Prims_int b);

extern Prims_int FStar_UInt_logxor(Prims_pos n, Prims_int a, Prims_int b);

extern Prims_int FStar_UInt_logor(Prims_pos n, Prims_int a, Prims_int b);

extern Prims_int FStar_UInt_lognot(Prims_pos n, Prims_int a);

extern Prims_int FStar_UInt_minus(Prims_pos n, Prims_int a);

extern Prims_int FStar_UInt_shift_left(Prims_pos n, Prims_int a, Prims_int s);

extern Prims_int FStar_UInt_shift_right(Prims_pos n, Prims_int a, Prims_int s);

extern bool FStar_UInt_msb(Prims_pos n, Prims_int a);

extern Prims_list__bool *FStar_UInt_zero_extend_vec(Prims_pos n, Prims_list__bool *a);

extern Prims_list__bool *FStar_UInt_one_extend_vec(Prims_pos n, Prims_list__bool *a);

extern Prims_int FStar_UInt_zero_extend(Prims_pos n, Prims_int a);

extern Prims_int FStar_UInt_one_extend(Prims_pos n, Prims_int a);

#define __FStar_UInt_H_DEFINED
#endif
