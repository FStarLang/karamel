/*
  Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
  Licensed under the Apache 2.0 and MIT Licenses.
*/


#ifndef KRML_HEADER_FStar_Order_H
#define KRML_HEADER_FStar_Order_H

#include <inttypes.h>
#include "krmllib.h"
#include "krml/internal/compat.h"
#include "krml/internal/target.h"

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

FStar_Order_order FStar_Order_lex(FStar_Order_order o1, FStar_Order_order (*o2)(void));

FStar_Order_order FStar_Order_order_from_int(krml_checked_int_t i);

krml_checked_int_t FStar_Order_int_of_order(FStar_Order_order uu___);

FStar_Order_order FStar_Order_compare_int(krml_checked_int_t i, krml_checked_int_t j);


#define KRML_HEADER_FStar_Order_H_DEFINED
#endif /* KRML_HEADER_FStar_Order_H */
