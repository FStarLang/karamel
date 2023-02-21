/*
  Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
  Licensed under the Apache 2.0 License.
*/


#include "FStar_Algebra_CommMonoid_Equiv.h"

bool FStar_Algebra_CommMonoid_Equiv_uu___is_EQ(FStar_Algebra_CommMonoid_Equiv_equiv projectee)
{
  return true;
}

FStar_Algebra_CommMonoid_Equiv_equiv FStar_Algebra_CommMonoid_Equiv_equality_equiv(void)
{
  return FStar_Algebra_CommMonoid_Equiv_EQ;
}

FStar_Algebra_CommMonoid_Equiv_cm__Prims_int
FStar_Algebra_CommMonoid_Equiv_int_plus_cm =
  { .unit = (krml_checked_int_t)0, .mult = Prims_op_Addition };

FStar_Algebra_CommMonoid_Equiv_cm__Prims_int
FStar_Algebra_CommMonoid_Equiv_int_multiply_cm =
  { .unit = (krml_checked_int_t)1, .mult = Prims_op_Multiply };

