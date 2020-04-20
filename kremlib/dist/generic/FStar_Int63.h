/*
  Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
  Licensed under the Apache 2.0 License.
*/

#include <inttypes.h>
#include "kremlib.h"
#include "kremlin/internal/compat.h"
#include "kremlin/internal/target.h"

#ifndef __FStar_Int63_H
#define __FStar_Int63_H




extern Prims_int FStar_Int63_n;

extern Prims_int FStar_Int63_v(FStar_Int63_t x);

extern FStar_Int63_t FStar_Int63_int_to_t(Prims_int x);

extern FStar_Int63_t FStar_Int63_add(FStar_Int63_t a, FStar_Int63_t b);

extern FStar_Int63_t FStar_Int63_sub(FStar_Int63_t a, FStar_Int63_t b);

extern FStar_Int63_t FStar_Int63_mul(FStar_Int63_t a, FStar_Int63_t b);

extern FStar_Int63_t FStar_Int63_div(FStar_Int63_t a, FStar_Int63_t b);

extern FStar_Int63_t FStar_Int63_rem(FStar_Int63_t a, FStar_Int63_t b);

extern FStar_Int63_t FStar_Int63_logand(FStar_Int63_t x, FStar_Int63_t y);

extern FStar_Int63_t FStar_Int63_logxor(FStar_Int63_t x, FStar_Int63_t y);

extern FStar_Int63_t FStar_Int63_logor(FStar_Int63_t x, FStar_Int63_t y);

extern FStar_Int63_t FStar_Int63_lognot(FStar_Int63_t x);

/*
 If a is negative the result is implementation-defined 
*/
extern FStar_Int63_t FStar_Int63_shift_right(FStar_Int63_t a, uint32_t s);

/*
 If a is negative or a * pow2 s is not representable the result is undefined 
*/
extern FStar_Int63_t FStar_Int63_shift_left(FStar_Int63_t a, uint32_t s);

extern FStar_Int63_t FStar_Int63_shift_arithmetic_right(FStar_Int63_t a, uint32_t s);

extern bool FStar_Int63_eq(FStar_Int63_t a, FStar_Int63_t b);

extern bool FStar_Int63_gt(FStar_Int63_t a, FStar_Int63_t b);

extern bool FStar_Int63_gte(FStar_Int63_t a, FStar_Int63_t b);

extern bool FStar_Int63_lt(FStar_Int63_t a, FStar_Int63_t b);

extern bool FStar_Int63_lte(FStar_Int63_t a, FStar_Int63_t b);

extern FStar_Int63_t FStar_Int63_ct_abs(FStar_Int63_t a);

extern Prims_string FStar_Int63_to_string(FStar_Int63_t uu____503);

extern FStar_Int63_t FStar_Int63_of_string(Prims_string uu____515);

#define __FStar_Int63_H_DEFINED
#endif
