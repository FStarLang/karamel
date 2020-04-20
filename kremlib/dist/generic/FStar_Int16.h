/*
  Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
  Licensed under the Apache 2.0 License.
*/

#include <inttypes.h>
#include "kremlib.h"
#include "kremlin/internal/compat.h"
#include "kremlin/internal/target.h"

#ifndef __FStar_Int16_H
#define __FStar_Int16_H




extern Prims_int FStar_Int16_n;

extern bool FStar_Int16_uu___is_Mk(int16_t projectee);

extern Prims_int FStar_Int16___proj__Mk__item__v(int16_t projectee);

extern Prims_int FStar_Int16_v(int16_t x);

extern int16_t FStar_Int16_int_to_t(Prims_int x);

extern int16_t FStar_Int16_add(int16_t a, int16_t b);

extern int16_t FStar_Int16_sub(int16_t a, int16_t b);

extern int16_t FStar_Int16_mul(int16_t a, int16_t b);

extern int16_t FStar_Int16_div(int16_t a, int16_t b);

extern int16_t FStar_Int16_rem(int16_t a, int16_t b);

extern int16_t FStar_Int16_logand(int16_t x, int16_t y);

extern int16_t FStar_Int16_logxor(int16_t x, int16_t y);

extern int16_t FStar_Int16_logor(int16_t x, int16_t y);

extern int16_t FStar_Int16_lognot(int16_t x);

extern int16_t FStar_Int16_shift_right(int16_t a, uint32_t s);

extern int16_t FStar_Int16_shift_left(int16_t a, uint32_t s);

extern bool FStar_Int16_eq(int16_t a, int16_t b);

extern bool FStar_Int16_gt(int16_t a, int16_t b);

extern bool FStar_Int16_gte(int16_t a, int16_t b);

extern bool FStar_Int16_lt(int16_t a, int16_t b);

extern bool FStar_Int16_lte(int16_t a, int16_t b);

extern int16_t FStar_Int16_ct_abs(int16_t a);

extern Prims_string FStar_Int16_to_string(int16_t uu____636);

extern int16_t FStar_Int16_of_string(Prims_string uu____647);

#define __FStar_Int16_H_DEFINED
#endif
