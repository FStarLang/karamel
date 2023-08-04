/*
  Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
  Licensed under the Apache 2.0 License.
*/


#ifndef __FStar_UInt_H
#define __FStar_UInt_H

#include "FStar_BitVector.h"
#include <inttypes.h>
#include "krmllib.h"
#include "krml/internal/compat.h"
#include "krml/internal/target.h"

extern krml_checked_int_t FStar_UInt_max_int(krml_checked_int_t n);

extern krml_checked_int_t FStar_UInt_min_int(krml_checked_int_t n);

extern bool FStar_UInt_fits(krml_checked_int_t x, krml_checked_int_t n);

typedef void *FStar_UInt_size;

typedef krml_checked_int_t FStar_UInt_uint_t;

extern krml_checked_int_t FStar_UInt_zero(krml_checked_int_t n);

extern krml_checked_int_t FStar_UInt_pow2_n(krml_checked_int_t n, krml_checked_int_t p);

extern krml_checked_int_t FStar_UInt_one(krml_checked_int_t n);

extern krml_checked_int_t FStar_UInt_ones(krml_checked_int_t n);

extern krml_checked_int_t FStar_UInt_incr(krml_checked_int_t n, krml_checked_int_t a);

extern krml_checked_int_t FStar_UInt_decr(krml_checked_int_t n, krml_checked_int_t a);

extern krml_checked_int_t
FStar_UInt_incr_underspec(krml_checked_int_t n, krml_checked_int_t a);

extern krml_checked_int_t
FStar_UInt_decr_underspec(krml_checked_int_t n, krml_checked_int_t a);

extern krml_checked_int_t FStar_UInt_incr_mod(krml_checked_int_t n, krml_checked_int_t a);

extern krml_checked_int_t FStar_UInt_decr_mod(krml_checked_int_t n, krml_checked_int_t a);

extern krml_checked_int_t
FStar_UInt_add(krml_checked_int_t n, krml_checked_int_t a, krml_checked_int_t b);

extern krml_checked_int_t
FStar_UInt_add_underspec(krml_checked_int_t n, krml_checked_int_t a, krml_checked_int_t b);

extern krml_checked_int_t
FStar_UInt_add_mod(krml_checked_int_t n, krml_checked_int_t a, krml_checked_int_t b);

extern krml_checked_int_t
FStar_UInt_sub(krml_checked_int_t n, krml_checked_int_t a, krml_checked_int_t b);

extern krml_checked_int_t
FStar_UInt_sub_underspec(krml_checked_int_t n, krml_checked_int_t a, krml_checked_int_t b);

extern krml_checked_int_t
FStar_UInt_sub_mod(krml_checked_int_t n, krml_checked_int_t a, krml_checked_int_t b);

extern krml_checked_int_t
FStar_UInt_mul(krml_checked_int_t n, krml_checked_int_t a, krml_checked_int_t b);

extern krml_checked_int_t
FStar_UInt_mul_underspec(krml_checked_int_t n, krml_checked_int_t a, krml_checked_int_t b);

extern krml_checked_int_t
FStar_UInt_mul_mod(krml_checked_int_t n, krml_checked_int_t a, krml_checked_int_t b);

extern krml_checked_int_t
FStar_UInt_mul_div(krml_checked_int_t n, krml_checked_int_t a, krml_checked_int_t b);

extern krml_checked_int_t
FStar_UInt_div(krml_checked_int_t n, krml_checked_int_t a, krml_checked_int_t b);

extern krml_checked_int_t
FStar_UInt_div_underspec(krml_checked_int_t n, krml_checked_int_t a, krml_checked_int_t b);

extern krml_checked_int_t
FStar_UInt_udiv(krml_checked_int_t n, krml_checked_int_t a, krml_checked_int_t b);

extern krml_checked_int_t
FStar_UInt_mod(krml_checked_int_t n, krml_checked_int_t a, krml_checked_int_t b);

extern bool FStar_UInt_eq(krml_checked_int_t n, krml_checked_int_t a, krml_checked_int_t b);

extern bool FStar_UInt_gt(krml_checked_int_t n, krml_checked_int_t a, krml_checked_int_t b);

extern bool FStar_UInt_gte(krml_checked_int_t n, krml_checked_int_t a, krml_checked_int_t b);

extern bool FStar_UInt_lt(krml_checked_int_t n, krml_checked_int_t a, krml_checked_int_t b);

extern bool FStar_UInt_lte(krml_checked_int_t n, krml_checked_int_t a, krml_checked_int_t b);

extern krml_checked_int_t FStar_UInt_to_uint_t(krml_checked_int_t m, krml_checked_int_t a);

extern Prims_list__bool *FStar_UInt_to_vec(krml_checked_int_t n, krml_checked_int_t num);

extern krml_checked_int_t FStar_UInt_from_vec(krml_checked_int_t n, Prims_list__bool *vec);

extern bool FStar_UInt_nth(krml_checked_int_t n, krml_checked_int_t a, krml_checked_int_t i);

extern krml_checked_int_t
FStar_UInt_logand(krml_checked_int_t n, krml_checked_int_t a, krml_checked_int_t b);

extern krml_checked_int_t
FStar_UInt_logxor(krml_checked_int_t n, krml_checked_int_t a, krml_checked_int_t b);

extern krml_checked_int_t
FStar_UInt_logor(krml_checked_int_t n, krml_checked_int_t a, krml_checked_int_t b);

extern krml_checked_int_t FStar_UInt_lognot(krml_checked_int_t n, krml_checked_int_t a);

extern krml_checked_int_t FStar_UInt_minus(krml_checked_int_t n, krml_checked_int_t a);

extern krml_checked_int_t
FStar_UInt_shift_left(krml_checked_int_t n, krml_checked_int_t a, krml_checked_int_t s);

extern krml_checked_int_t
FStar_UInt_shift_right(krml_checked_int_t n, krml_checked_int_t a, krml_checked_int_t s);

extern bool FStar_UInt_msb(krml_checked_int_t n, krml_checked_int_t a);

extern Prims_list__bool *FStar_UInt_zero_extend_vec(krml_checked_int_t n, Prims_list__bool *a);

extern Prims_list__bool *FStar_UInt_one_extend_vec(krml_checked_int_t n, Prims_list__bool *a);

extern krml_checked_int_t FStar_UInt_zero_extend(krml_checked_int_t n, krml_checked_int_t a);

extern krml_checked_int_t FStar_UInt_one_extend(krml_checked_int_t n, krml_checked_int_t a);


#define __FStar_UInt_H_DEFINED
#endif
