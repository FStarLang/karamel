/*
  Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
  Licensed under the Apache 2.0 License.
*/

#include <inttypes.h>
#include "kremlib.h"
#include "kremlin/internal/compat.h"
#include "kremlin/internal/target.h"

#ifndef __FStar_UInt63_H
#define __FStar_UInt63_H




extern Prims_int FStar_UInt63_n;

extern Prims_int FStar_UInt63_v(FStar_UInt63_t x);

extern FStar_UInt63_t FStar_UInt63_uint_to_t(Prims_int x);

extern FStar_UInt63_t FStar_UInt63_add(FStar_UInt63_t a, FStar_UInt63_t b);

extern FStar_UInt63_t FStar_UInt63_add_underspec(FStar_UInt63_t a, FStar_UInt63_t b);

extern FStar_UInt63_t FStar_UInt63_add_mod(FStar_UInt63_t a, FStar_UInt63_t b);

extern FStar_UInt63_t FStar_UInt63_sub(FStar_UInt63_t a, FStar_UInt63_t b);

extern FStar_UInt63_t FStar_UInt63_sub_underspec(FStar_UInt63_t a, FStar_UInt63_t b);

extern FStar_UInt63_t FStar_UInt63_sub_mod(FStar_UInt63_t a, FStar_UInt63_t b);

extern FStar_UInt63_t FStar_UInt63_mul(FStar_UInt63_t a, FStar_UInt63_t b);

extern FStar_UInt63_t FStar_UInt63_mul_underspec(FStar_UInt63_t a, FStar_UInt63_t b);

extern FStar_UInt63_t FStar_UInt63_mul_mod(FStar_UInt63_t a, FStar_UInt63_t b);

extern FStar_UInt63_t FStar_UInt63_mul_div(FStar_UInt63_t a, FStar_UInt63_t b);

extern FStar_UInt63_t FStar_UInt63_div(FStar_UInt63_t a, FStar_UInt63_t b);

extern FStar_UInt63_t FStar_UInt63_rem(FStar_UInt63_t a, FStar_UInt63_t b);

extern FStar_UInt63_t FStar_UInt63_logand(FStar_UInt63_t x, FStar_UInt63_t y);

extern FStar_UInt63_t FStar_UInt63_logxor(FStar_UInt63_t x, FStar_UInt63_t y);

extern FStar_UInt63_t FStar_UInt63_logor(FStar_UInt63_t x, FStar_UInt63_t y);

extern FStar_UInt63_t FStar_UInt63_lognot(FStar_UInt63_t x);

extern FStar_UInt63_t FStar_UInt63_shift_right(FStar_UInt63_t a, uint32_t s);

extern FStar_UInt63_t FStar_UInt63_shift_left(FStar_UInt63_t a, uint32_t s);

extern bool FStar_UInt63_eq(FStar_UInt63_t a, FStar_UInt63_t b);

extern bool FStar_UInt63_gt(FStar_UInt63_t a, FStar_UInt63_t b);

extern bool FStar_UInt63_gte(FStar_UInt63_t a, FStar_UInt63_t b);

extern bool FStar_UInt63_lt(FStar_UInt63_t a, FStar_UInt63_t b);

extern bool FStar_UInt63_lte(FStar_UInt63_t a, FStar_UInt63_t b);

extern FStar_UInt63_t FStar_UInt63_minus(FStar_UInt63_t a);

extern uint32_t FStar_UInt63_n_minus_one;

extern FStar_UInt63_t FStar_UInt63_eq_mask(FStar_UInt63_t a, FStar_UInt63_t b);

extern FStar_UInt63_t FStar_UInt63_gte_mask(FStar_UInt63_t a, FStar_UInt63_t b);

extern Prims_string FStar_UInt63_to_string(FStar_UInt63_t uu____716);

extern FStar_UInt63_t FStar_UInt63_of_string(Prims_string uu____728);

#define __FStar_UInt63_H_DEFINED
#endif
