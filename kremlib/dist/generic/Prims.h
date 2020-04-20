/*
  Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
  Licensed under the Apache 2.0 License.
*/

#include <inttypes.h>
#include "kremlib.h"
#include "kremlin/internal/compat.h"
#include "kremlin/internal/target.h"

#ifndef __Prims_H
#define __Prims_H




extern krml_checked_int_t Prims_op_Multiply(krml_checked_int_t x, krml_checked_int_t y);

extern krml_checked_int_t Prims_op_Division(krml_checked_int_t x, krml_checked_int_t y);

extern krml_checked_int_t Prims_op_Subtraction(krml_checked_int_t x, krml_checked_int_t y);

extern krml_checked_int_t Prims_op_Addition(krml_checked_int_t x, krml_checked_int_t y);

extern krml_checked_int_t Prims_op_Minus(krml_checked_int_t x, krml_checked_int_t y);

extern krml_checked_int_t Prims_op_Modulus(krml_checked_int_t x, krml_checked_int_t y);

extern bool Prims_op_LessThanOrEqual(krml_checked_int_t x0, krml_checked_int_t x1);

extern bool Prims_op_GreaterThan(krml_checked_int_t x0, krml_checked_int_t x1);

extern bool Prims_op_GreaterThanOrEqual(krml_checked_int_t x0, krml_checked_int_t x1);

extern bool Prims_op_LessThan(krml_checked_int_t x0, krml_checked_int_t x1);

extern krml_checked_int_t Prims_pow2(krml_checked_int_t x0);

extern krml_checked_int_t Prims_abs(krml_checked_int_t x0);

extern Prims_string Prims_strcat(Prims_string x0, Prims_string x1);

extern Prims_string Prims_string_of_int(krml_checked_int_t x0);

typedef void *Prims_prop;

#define __Prims_H_DEFINED
#endif
