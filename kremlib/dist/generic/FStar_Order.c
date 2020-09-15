/*
  Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
  Licensed under the Apache 2.0 License.
*/


#include "FStar_Order.h"

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

static bool __neq__FStar_Order_order(FStar_Order_order y, FStar_Order_order x)
{
  switch (x)
  {
    case FStar_Order_Lt:
      {
        switch (y)
        {
          case FStar_Order_Lt:
            {
              return false;
            }
          default:
            {
              return true;
            }
        }
        break;
      }
    case FStar_Order_Eq:
      {
        switch (y)
        {
          case FStar_Order_Eq:
            {
              return false;
            }
          default:
            {
              return true;
            }
        }
        break;
      }
    case FStar_Order_Gt:
      {
        switch (y)
        {
          case FStar_Order_Gt:
            {
              return false;
            }
          default:
            {
              return true;
            }
        }
        break;
      }
    default:
      {
        return true;
      }
  }
}

bool FStar_Order_ge(FStar_Order_order o)
{
  return __neq__FStar_Order_order(o, FStar_Order_Lt);
}

bool FStar_Order_le(FStar_Order_order o)
{
  return __neq__FStar_Order_order(o, FStar_Order_Gt);
}

bool FStar_Order_ne(FStar_Order_order o)
{
  return __neq__FStar_Order_order(o, FStar_Order_Eq);
}

static bool __eq__FStar_Order_order(FStar_Order_order y, FStar_Order_order x)
{
  switch (x)
  {
    case FStar_Order_Lt:
      {
        switch (y)
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
        break;
      }
    case FStar_Order_Eq:
      {
        switch (y)
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
        break;
      }
    case FStar_Order_Gt:
      {
        switch (y)
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
        break;
      }
    default:
      {
        return false;
      }
  }
}

bool FStar_Order_gt(FStar_Order_order o)
{
  return __eq__FStar_Order_order(o, FStar_Order_Gt);
}

bool FStar_Order_lt(FStar_Order_order o)
{
  return __eq__FStar_Order_order(o, FStar_Order_Lt);
}

bool FStar_Order_eq(FStar_Order_order o)
{
  return __eq__FStar_Order_order(o, FStar_Order_Eq);
}

FStar_Order_order FStar_Order_lex(FStar_Order_order o1, FStar_Order_order (*o2)())
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
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

FStar_Order_order FStar_Order_order_from_int(Prims_int i)
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

Prims_int FStar_Order_int_of_order(FStar_Order_order uu___)
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
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

FStar_Order_order FStar_Order_compare_int(Prims_int i, Prims_int j)
{
  return FStar_Order_order_from_int(Prims_op_Subtraction(i, j));
}

