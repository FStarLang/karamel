/*
  Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
  Licensed under the Apache 2.0 License.
*/

#include <inttypes.h>
#include "kremlib.h"
#include "kremlin/internal/compat.h"
#include "kremlin/internal/target.h"

#ifndef __FStar_Int32_H
#define __FStar_Int32_H




extern Prims_int FStar_Int32_n;

extern bool FStar_Int32_uu___is_Mk(int32_t projectee);

extern Prims_int FStar_Int32___proj__Mk__item__v(int32_t projectee);

extern Prims_int FStar_Int32_v(int32_t x);

extern int32_t FStar_Int32_int_to_t(Prims_int x);

extern int32_t FStar_Int32_add(int32_t a, int32_t b);

extern int32_t FStar_Int32_sub(int32_t a, int32_t b);

extern int32_t FStar_Int32_mul(int32_t a, int32_t b);

extern int32_t FStar_Int32_div(int32_t a, int32_t b);

extern int32_t FStar_Int32_rem(int32_t a, int32_t b);

extern int32_t FStar_Int32_logand(int32_t x, int32_t y);

extern int32_t FStar_Int32_logxor(int32_t x, int32_t y);

extern int32_t FStar_Int32_logor(int32_t x, int32_t y);

extern int32_t FStar_Int32_lognot(int32_t x);

extern int32_t FStar_Int32_shift_right(int32_t a, uint32_t s);

extern int32_t FStar_Int32_shift_left(int32_t a, uint32_t s);

extern bool FStar_Int32_eq(int32_t a, int32_t b);

extern bool FStar_Int32_gt(int32_t a, int32_t b);

extern bool FStar_Int32_gte(int32_t a, int32_t b);

extern bool FStar_Int32_lt(int32_t a, int32_t b);

extern bool FStar_Int32_lte(int32_t a, int32_t b);

extern int32_t FStar_Int32_ct_abs(int32_t a);

extern Prims_string FStar_Int32_to_string(int32_t uu____636);

extern int32_t FStar_Int32_of_string(Prims_string uu____647);

#define __FStar_Int32_H_DEFINED
#endif
