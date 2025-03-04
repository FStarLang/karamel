/*
  Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
  Licensed under the Apache 2.0 and MIT Licenses.
*/


#include "FStar_Order.h"

#include "Prims.h"

bool FStar_Order_uu___is_Lt(FStar_Order_order projectee)
{
  switch (projectee)
  {
    case FStar_Order_Lt:
      {
        return true;
      }
    default:
      {
        return false;
      }
  }
}

bool FStar_Order_uu___is_Eq(FStar_Order_order projectee)
{
  switch (projectee)
  {
    case FStar_Order_Eq:
      {
        return true;
      }
    default:
      {
        return false;
      }
  }
}

bool FStar_Order_uu___is_Gt(FStar_Order_order projectee)
{
  switch (projectee)
  {
    case FStar_Order_Gt:
      {
        return true;
      }
    default:
      {
        return false;
      }
  }
}

bool FStar_Order_ge(FStar_Order_order o)
{
  return o != FStar_Order_Lt;
}

bool FStar_Order_le(FStar_Order_order o)
{
  return o != FStar_Order_Gt;
}

bool FStar_Order_ne(FStar_Order_order o)
{
  return o != FStar_Order_Eq;
}

bool FStar_Order_gt(FStar_Order_order o)
{
  return o == FStar_Order_Gt;
}

bool FStar_Order_lt(FStar_Order_order o)
{
  return o == FStar_Order_Lt;
}

bool FStar_Order_eq(FStar_Order_order o)
{
  return o == FStar_Order_Eq;
}

FStar_Order_order FStar_Order_lex(FStar_Order_order o1, FStar_Order_order (*o2)(void))
{
  switch (o1)
  {
    case FStar_Order_Lt:
      {
        return FStar_Order_Lt;
      }
    case FStar_Order_Eq:
      {
        return o2();
      }
    case FStar_Order_Gt:
      {
        return FStar_Order_Gt;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

FStar_Order_order FStar_Order_order_from_int(krml_checked_int_t i)
{
  if (Prims_op_LessThan(i, (krml_checked_int_t)0))
  {
    return FStar_Order_Lt;
  }
  else if (i == (krml_checked_int_t)0)
  {
    return FStar_Order_Eq;
  }
  else
  {
    return FStar_Order_Gt;
  }
}

krml_checked_int_t FStar_Order_int_of_order(FStar_Order_order uu___)
{
  switch (uu___)
  {
    case FStar_Order_Lt:
      {
        return (krml_checked_int_t)-1;
      }
    case FStar_Order_Eq:
      {
        return (krml_checked_int_t)0;
      }
    case FStar_Order_Gt:
      {
        return (krml_checked_int_t)1;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

FStar_Order_order FStar_Order_compare_int(krml_checked_int_t i, krml_checked_int_t j)
{
  return FStar_Order_order_from_int(Prims_op_Subtraction(i, j));
}

