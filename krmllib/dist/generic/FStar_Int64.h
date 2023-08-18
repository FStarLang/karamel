/*
  Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
  Licensed under the Apache 2.0 License.
*/


#ifndef __FStar_Int64_H
#define __FStar_Int64_H

#include <inttypes.h>
#include "krmllib.h"
#include "krml/internal/compat.h"
#include "krml/internal/target.h"

extern krml_checked_int_t FStar_Int64_n;

extern bool FStar_Int64_uu___is_Mk(int64_t projectee);

extern krml_checked_int_t FStar_Int64___proj__Mk__item__v(int64_t projectee);

extern krml_checked_int_t FStar_Int64_v(int64_t x);

extern int64_t FStar_Int64_int_to_t(krml_checked_int_t x);

extern int64_t FStar_Int64_zero;

extern int64_t FStar_Int64_one;

extern int64_t FStar_Int64_add(int64_t a, int64_t b);

extern int64_t FStar_Int64_sub(int64_t a, int64_t b);

extern int64_t FStar_Int64_mul(int64_t a, int64_t b);

extern int64_t FStar_Int64_div(int64_t a, int64_t b);

extern int64_t FStar_Int64_rem(int64_t a, int64_t b);

extern int64_t FStar_Int64_logand(int64_t x, int64_t y);

extern int64_t FStar_Int64_logxor(int64_t x, int64_t y);

extern int64_t FStar_Int64_logor(int64_t x, int64_t y);

extern int64_t FStar_Int64_lognot(int64_t x);

extern int64_t FStar_Int64_shift_right(int64_t a, uint32_t s);

extern int64_t FStar_Int64_shift_left(int64_t a, uint32_t s);

extern bool FStar_Int64_eq(int64_t a, int64_t b);

extern bool FStar_Int64_gt(int64_t a, int64_t b);

extern bool FStar_Int64_gte(int64_t a, int64_t b);

extern bool FStar_Int64_lt(int64_t a, int64_t b);

extern bool FStar_Int64_lte(int64_t a, int64_t b);

extern int64_t FStar_Int64_ct_abs(int64_t a);

extern Prims_string FStar_Int64_to_string(int64_t uu___);

extern int64_t FStar_Int64_of_string(Prims_string uu___);


#define __FStar_Int64_H_DEFINED
#endif
