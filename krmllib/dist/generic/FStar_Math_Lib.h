/*
  Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
  Licensed under the Apache 2.0 and MIT Licenses.
*/


#ifndef FStar_Math_Lib_H
#define FStar_Math_Lib_H

#include <inttypes.h>
#include "krmllib.h"
#include "krml/internal/compat.h"
#include "krml/internal/target.h"

extern krml_checked_int_t FStar_Math_Lib_log_2(krml_checked_int_t x);

extern krml_checked_int_t FStar_Math_Lib_powx(krml_checked_int_t x, krml_checked_int_t n);

extern krml_checked_int_t FStar_Math_Lib_abs(krml_checked_int_t x);

extern krml_checked_int_t FStar_Math_Lib_max(krml_checked_int_t x, krml_checked_int_t y);

extern krml_checked_int_t FStar_Math_Lib_min(krml_checked_int_t x, krml_checked_int_t y);

extern krml_checked_int_t FStar_Math_Lib_div(krml_checked_int_t a, krml_checked_int_t b);

extern krml_checked_int_t
FStar_Math_Lib_div_non_eucl(krml_checked_int_t a, krml_checked_int_t b);

extern krml_checked_int_t
FStar_Math_Lib_shift_left(krml_checked_int_t v, krml_checked_int_t i);

extern krml_checked_int_t
FStar_Math_Lib_arithmetic_shift_right(krml_checked_int_t v, krml_checked_int_t i);

extern krml_checked_int_t
FStar_Math_Lib_signed_modulo(krml_checked_int_t v, krml_checked_int_t p);

extern krml_checked_int_t
FStar_Math_Lib_op_Plus_Percent(krml_checked_int_t a, krml_checked_int_t p);


#define FStar_Math_Lib_H_DEFINED
#endif /* FStar_Math_Lib_H */
