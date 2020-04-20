/*
  Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
  Licensed under the Apache 2.0 License.
*/

#include <inttypes.h>
#include "kremlib.h"
#include "kremlin/internal/compat.h"
#include "kremlin/internal/target.h"

#ifndef __FStar_Int8_H
#define __FStar_Int8_H




extern Prims_int FStar_Int8_n;

extern bool FStar_Int8_uu___is_Mk(int8_t projectee);

extern Prims_int FStar_Int8___proj__Mk__item__v(int8_t projectee);

extern Prims_int FStar_Int8_v(int8_t x);

extern int8_t FStar_Int8_int_to_t(Prims_int x);

extern int8_t FStar_Int8_add(int8_t a, int8_t b);

extern int8_t FStar_Int8_sub(int8_t a, int8_t b);

extern int8_t FStar_Int8_mul(int8_t a, int8_t b);

extern int8_t FStar_Int8_div(int8_t a, int8_t b);

extern int8_t FStar_Int8_rem(int8_t a, int8_t b);

extern int8_t FStar_Int8_logand(int8_t x, int8_t y);

extern int8_t FStar_Int8_logxor(int8_t x, int8_t y);

extern int8_t FStar_Int8_logor(int8_t x, int8_t y);

extern int8_t FStar_Int8_lognot(int8_t x);

extern int8_t FStar_Int8_shift_right(int8_t a, uint32_t s);

extern int8_t FStar_Int8_shift_left(int8_t a, uint32_t s);

extern bool FStar_Int8_eq(int8_t a, int8_t b);

extern bool FStar_Int8_gt(int8_t a, int8_t b);

extern bool FStar_Int8_gte(int8_t a, int8_t b);

extern bool FStar_Int8_lt(int8_t a, int8_t b);

extern bool FStar_Int8_lte(int8_t a, int8_t b);

extern int8_t FStar_Int8_ct_abs(int8_t a);

extern Prims_string FStar_Int8_to_string(int8_t uu____636);

extern int8_t FStar_Int8_of_string(Prims_string uu____647);

#define __FStar_Int8_H_DEFINED
#endif
