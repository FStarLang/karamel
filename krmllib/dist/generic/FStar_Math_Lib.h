/*
  Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
  Licensed under the Apache 2.0 License.
*/


#ifndef __FStar_Math_Lib_H
#define __FStar_Math_Lib_H

#include <inttypes.h>
#include "krmllib.h"
#include "krml/internal/compat.h"
#include "krml/internal/target.h"

extern Prims_int FStar_Math_Lib_log_2(Prims_pos x);

extern Prims_int FStar_Math_Lib_powx(Prims_int x, Prims_int n);

extern Prims_int FStar_Math_Lib_abs(Prims_int x);

extern Prims_int FStar_Math_Lib_max(Prims_int x, Prims_int y);

extern Prims_int FStar_Math_Lib_min(Prims_int x, Prims_int y);

extern Prims_int FStar_Math_Lib_div(Prims_int a, Prims_pos b);

extern Prims_int FStar_Math_Lib_div_non_eucl(Prims_int a, Prims_pos b);

extern Prims_int FStar_Math_Lib_shift_left(Prims_int v, Prims_int i);

extern Prims_int FStar_Math_Lib_arithmetic_shift_right(Prims_int v, Prims_int i);

extern Prims_int FStar_Math_Lib_signed_modulo(Prims_int v, Prims_pos p);

extern Prims_int FStar_Math_Lib_op_Plus_Percent(Prims_int a, Prims_pos p);


#define __FStar_Math_Lib_H_DEFINED
#endif
