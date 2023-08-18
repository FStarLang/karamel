/*
  Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
  Licensed under the Apache 2.0 License.
*/


#ifndef __FStar_BV_H
#define __FStar_BV_H

#include "Prims.h"
#include "FStar_UInt.h"
#include "FStar_BitVector.h"
#include <inttypes.h>
#include "krmllib.h"
#include "krml/internal/compat.h"
#include "krml/internal/target.h"

typedef Prims_list__bool *FStar_BV_bv_t;

Prims_list__bool *FStar_List_Tot_Base_append__bool(Prims_list__bool *x, Prims_list__bool *y);

Prims_list__bool *FStar_Seq_Base_append__bool(Prims_list__bool *s1, Prims_list__bool *s2);

Prims_list__bool *FStar_Seq_Base_create__bool(krml_checked_int_t len, bool v);

Prims_list__bool
*FStar_BV_bv_uext(krml_checked_int_t n, krml_checked_int_t i, Prims_list__bool *a);

extern Prims_list__bool *(*FStar_BV_int2bv)(krml_checked_int_t x0, krml_checked_int_t x1);

extern krml_checked_int_t (*FStar_BV_bv2int)(krml_checked_int_t x0, Prims_list__bool *x1);

Prims_list__bool *FStar_Seq_Base_empty__bool(void);

Prims_list__bool *FStar_Seq_Base_op_At_Bar__bool(Prims_list__bool *s1, Prims_list__bool *s2);

Prims_list__bool *FStar_Seq_Properties_seq_of_list__bool(Prims_list__bool *l);

Prims_list__bool *FStar_BV_list2bv(krml_checked_int_t n, Prims_list__bool *l);

krml_checked_int_t FStar_List_Tot_Base_length__bool(Prims_list__bool *uu___);

krml_checked_int_t FStar_Seq_Base_length__bool(Prims_list__bool *s);

bool FStar_List_Tot_Base_hd__bool(Prims_list__bool *uu___);

Prims_list__bool *FStar_List_Tot_Base_tail__bool(Prims_list__bool *uu___);

extern Prims_list__bool *(*FStar_List_Tot_Base_tl__bool)(Prims_list__bool *x0);

bool FStar_List_Tot_Base_index__bool(Prims_list__bool *l, krml_checked_int_t i);

bool FStar_Seq_Base_index__bool(Prims_list__bool *s, krml_checked_int_t i);

extern Prims_list__bool
*(*FStar_Seq_Base_slice__bool)(
  Prims_list__bool *x0,
  krml_checked_int_t x1,
  krml_checked_int_t x2
);

Prims_list__bool *FStar_Seq_Properties_seq_to_list__bool(Prims_list__bool *s);

Prims_list__bool *FStar_BV_bv2list(krml_checked_int_t n, Prims_list__bool *s);

extern Prims_list__bool
*(*FStar_BV_bvand)(krml_checked_int_t x0, Prims_list__bool *x1, Prims_list__bool *x2);

extern Prims_list__bool
*(*FStar_BV_bvxor)(krml_checked_int_t x0, Prims_list__bool *x1, Prims_list__bool *x2);

extern Prims_list__bool
*(*FStar_BV_bvor)(krml_checked_int_t x0, Prims_list__bool *x1, Prims_list__bool *x2);

extern Prims_list__bool *(*FStar_BV_bvnot)(krml_checked_int_t x0, Prims_list__bool *x1);

extern Prims_list__bool
*(*FStar_BV_bvshl)(krml_checked_int_t x0, Prims_list__bool *x1, krml_checked_int_t x2);

extern Prims_list__bool
*(*FStar_BV_bvshr)(krml_checked_int_t x0, Prims_list__bool *x1, krml_checked_int_t x2);

Prims_list__bool *FStar_BV_bv_zero(krml_checked_int_t n);

bool FStar_BV_bvult(krml_checked_int_t n, Prims_list__bool *a, Prims_list__bool *b);

Prims_list__bool
*FStar_BV_bvadd(krml_checked_int_t n, Prims_list__bool *a, Prims_list__bool *b);

Prims_list__bool
*FStar_BV_bvsub(krml_checked_int_t n, Prims_list__bool *a, Prims_list__bool *b);

Prims_list__bool
*FStar_BV_bvdiv(krml_checked_int_t n, Prims_list__bool *a, krml_checked_int_t b);

Prims_list__bool
*FStar_BV_bvmod(krml_checked_int_t n, Prims_list__bool *a, krml_checked_int_t b);

Prims_list__bool
*FStar_BV_bvmul(krml_checked_int_t n, Prims_list__bool *a, krml_checked_int_t b);


#define __FStar_BV_H_DEFINED
#endif
