/*
  Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
  Licensed under the Apache 2.0 License.
*/


#ifndef __FStar_Algebra_CommMonoid_Equiv_H
#define __FStar_Algebra_CommMonoid_Equiv_H



#include "Prims.h"
#include <inttypes.h>
#include "krmllib.h"
#include "krml/internal/compat.h"
#include "krml/internal/target.h"
#define FStar_Algebra_CommMonoid_Equiv_EQ 0

typedef uint8_t FStar_Algebra_CommMonoid_Equiv_equiv;

bool FStar_Algebra_CommMonoid_Equiv_uu___is_EQ(FStar_Algebra_CommMonoid_Equiv_equiv projectee);

FStar_Algebra_CommMonoid_Equiv_equiv FStar_Algebra_CommMonoid_Equiv_equality_equiv();

typedef struct FStar_Algebra_CommMonoid_Equiv_cm__Prims_int_s
{
  Prims_int unit;
  Prims_int (*mult)(Prims_int x0, Prims_int x1);
}
FStar_Algebra_CommMonoid_Equiv_cm__Prims_int;

extern FStar_Algebra_CommMonoid_Equiv_cm__Prims_int FStar_Algebra_CommMonoid_Equiv_int_plus_cm;

extern FStar_Algebra_CommMonoid_Equiv_cm__Prims_int
FStar_Algebra_CommMonoid_Equiv_int_multiply_cm;


#define __FStar_Algebra_CommMonoid_Equiv_H_DEFINED
#endif
