/*
  Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
  Licensed under the Apache 2.0 and MIT Licenses.
*/


#ifndef KRML_HEADER_FStar_Int_H
#define KRML_HEADER_FStar_Int_H

#include "FStar_BitVector.h"
#include <inttypes.h>
#include "krmllib.h"
#include "krml/internal/compat.h"
#include "krml/internal/target.h"

extern krml_checked_int_t FStar_Int_max_int(krml_checked_int_t n);

extern krml_checked_int_t FStar_Int_min_int(krml_checked_int_t n);

extern bool FStar_Int_fits(krml_checked_int_t x, krml_checked_int_t n);

typedef void *FStar_Int_size;

typedef krml_checked_int_t FStar_Int_int_t;

extern krml_checked_int_t FStar_Int_op_Slash(krml_checked_int_t a, krml_checked_int_t b);

extern krml_checked_int_t FStar_Int_op_At_Percent(krml_checked_int_t v, krml_checked_int_t p);

extern krml_checked_int_t FStar_Int_zero(krml_checked_int_t n);

extern krml_checked_int_t FStar_Int_pow2_n(krml_checked_int_t n, krml_checked_int_t p);

extern krml_checked_int_t FStar_Int_pow2_minus_one(krml_checked_int_t n, krml_checked_int_t m);

extern krml_checked_int_t FStar_Int_one(krml_checked_int_t n);

extern krml_checked_int_t FStar_Int_ones(krml_checked_int_t n);

extern krml_checked_int_t FStar_Int_incr(krml_checked_int_t n, krml_checked_int_t a);

extern krml_checked_int_t FStar_Int_decr(krml_checked_int_t n, krml_checked_int_t a);

extern krml_checked_int_t FStar_Int_incr_underspec(krml_checked_int_t n, krml_checked_int_t a);

extern krml_checked_int_t FStar_Int_decr_underspec(krml_checked_int_t n, krml_checked_int_t a);

extern krml_checked_int_t FStar_Int_incr_mod(krml_checked_int_t n, krml_checked_int_t a);

extern krml_checked_int_t FStar_Int_decr_mod(krml_checked_int_t n, krml_checked_int_t a);

extern krml_checked_int_t
FStar_Int_add(krml_checked_int_t n, krml_checked_int_t a, krml_checked_int_t b);

extern krml_checked_int_t
FStar_Int_add_underspec(krml_checked_int_t n, krml_checked_int_t a, krml_checked_int_t b);

extern krml_checked_int_t
FStar_Int_add_mod(krml_checked_int_t n, krml_checked_int_t a, krml_checked_int_t b);

extern krml_checked_int_t
FStar_Int_sub(krml_checked_int_t n, krml_checked_int_t a, krml_checked_int_t b);

extern krml_checked_int_t
FStar_Int_sub_underspec(krml_checked_int_t n, krml_checked_int_t a, krml_checked_int_t b);

extern krml_checked_int_t
FStar_Int_sub_mod(krml_checked_int_t n, krml_checked_int_t a, krml_checked_int_t b);

extern krml_checked_int_t
FStar_Int_mul(krml_checked_int_t n, krml_checked_int_t a, krml_checked_int_t b);

extern krml_checked_int_t
FStar_Int_mul_underspec(krml_checked_int_t n, krml_checked_int_t a, krml_checked_int_t b);

extern krml_checked_int_t
FStar_Int_mul_mod(krml_checked_int_t n, krml_checked_int_t a, krml_checked_int_t b);

extern krml_checked_int_t
FStar_Int_div(krml_checked_int_t n, krml_checked_int_t a, krml_checked_int_t b);

extern krml_checked_int_t
FStar_Int_div_underspec(krml_checked_int_t n, krml_checked_int_t a, krml_checked_int_t b);

extern krml_checked_int_t
FStar_Int_udiv(krml_checked_int_t n, krml_checked_int_t a, krml_checked_int_t b);

extern krml_checked_int_t
FStar_Int_mod(krml_checked_int_t n, krml_checked_int_t a, krml_checked_int_t b);

extern bool FStar_Int_eq(krml_checked_int_t n, krml_checked_int_t a, krml_checked_int_t b);

extern bool FStar_Int_ne(krml_checked_int_t n, krml_checked_int_t a, krml_checked_int_t b);

extern bool FStar_Int_gt(krml_checked_int_t n, krml_checked_int_t a, krml_checked_int_t b);

extern bool FStar_Int_gte(krml_checked_int_t n, krml_checked_int_t a, krml_checked_int_t b);

extern bool FStar_Int_lt(krml_checked_int_t n, krml_checked_int_t a, krml_checked_int_t b);

extern bool FStar_Int_lte(krml_checked_int_t n, krml_checked_int_t a, krml_checked_int_t b);

extern krml_checked_int_t FStar_Int_to_uint(krml_checked_int_t n, krml_checked_int_t x);

extern krml_checked_int_t FStar_Int_from_uint(krml_checked_int_t n, krml_checked_int_t x);

extern krml_checked_int_t FStar_Int_to_int_t(krml_checked_int_t m, krml_checked_int_t a);

extern Prims_list__bool *FStar_Int_to_vec(krml_checked_int_t n, krml_checked_int_t num);

extern krml_checked_int_t FStar_Int_from_vec(krml_checked_int_t n, Prims_list__bool *vec);

extern bool FStar_Int_nth(krml_checked_int_t n, krml_checked_int_t a, krml_checked_int_t i);

extern krml_checked_int_t
FStar_Int_logand(krml_checked_int_t n, krml_checked_int_t a, krml_checked_int_t b);

extern krml_checked_int_t
FStar_Int_logxor(krml_checked_int_t n, krml_checked_int_t a, krml_checked_int_t b);

extern krml_checked_int_t
FStar_Int_logor(krml_checked_int_t n, krml_checked_int_t a, krml_checked_int_t b);

extern krml_checked_int_t FStar_Int_lognot(krml_checked_int_t n, krml_checked_int_t a);

extern krml_checked_int_t FStar_Int_minus(krml_checked_int_t n, krml_checked_int_t a);

extern krml_checked_int_t
FStar_Int_shift_left(krml_checked_int_t n, krml_checked_int_t a, krml_checked_int_t s);

extern krml_checked_int_t
FStar_Int_shift_right(krml_checked_int_t n, krml_checked_int_t a, krml_checked_int_t s);

extern krml_checked_int_t
FStar_Int_shift_arithmetic_right(
  krml_checked_int_t n,
  krml_checked_int_t a,
  krml_checked_int_t s
);


#define KRML_HEADER_FStar_Int_H_DEFINED
#endif /* KRML_HEADER_FStar_Int_H */
