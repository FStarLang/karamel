/*
  Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
  Licensed under the Apache 2.0 License.
*/

#include <inttypes.h>
#include "kremlib.h"
#include "kremlin/internal/compat.h"
#include "kremlin/internal/target.h"

#ifndef __FStar_Order_H
#define __FStar_Order_H

#include "Prims.h"


#define FStar_Order_Lt 0
#define FStar_Order_Eq 1
#define FStar_Order_Gt 2

typedef uint8_t FStar_Order_order;

bool FStar_Order_uu___is_Lt(FStar_Order_order projectee);

bool FStar_Order_uu___is_Eq(FStar_Order_order projectee);

bool FStar_Order_uu___is_Gt(FStar_Order_order projectee);

bool FStar_Order_ge(FStar_Order_order o);

bool FStar_Order_le(FStar_Order_order o);

bool FStar_Order_ne(FStar_Order_order o);

bool FStar_Order_gt(FStar_Order_order o);

bool FStar_Order_lt(FStar_Order_order o);

bool FStar_Order_eq(FStar_Order_order o);

FStar_Order_order FStar_Order_lex(FStar_Order_order o1, FStar_Order_order (*o2)());

FStar_Order_order FStar_Order_order_from_int(Prims_int i);

Prims_int FStar_Order_int_of_order(FStar_Order_order uu___0_129);

FStar_Order_order FStar_Order_compare_int(Prims_int i, Prims_int j);

#define __FStar_Order_H_DEFINED
#endif
