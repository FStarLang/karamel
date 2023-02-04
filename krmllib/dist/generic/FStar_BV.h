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

Prims_list__bool *FStar_Seq_Base_create__bool(Prims_int len, bool v);

Prims_list__bool *FStar_BV_bv_uext(Prims_pos n, Prims_pos i, Prims_list__bool *a);

extern Prims_list__bool *(*FStar_BV_int2bv)(Prims_pos x0, Prims_int x1);

extern Prims_int (*FStar_BV_bv2int)(Prims_pos x0, Prims_list__bool *x1);

Prims_list__bool *FStar_Seq_Base_empty__bool(void);

Prims_list__bool *FStar_Seq_Base_op_At_Bar__bool(Prims_list__bool *s1, Prims_list__bool *s2);

Prims_list__bool *FStar_Seq_Properties_seq_of_list__bool(Prims_list__bool *l);

Prims_list__bool *FStar_BV_list2bv(Prims_pos n, Prims_list__bool *l);

Prims_int FStar_List_Tot_Base_length__bool(Prims_list__bool *uu___);

Prims_int FStar_Seq_Base_length__bool(Prims_list__bool *s);

bool FStar_List_Tot_Base_hd__bool(Prims_list__bool *uu___);

Prims_list__bool *FStar_List_Tot_Base_tail__bool(Prims_list__bool *uu___);

extern Prims_list__bool *(*FStar_List_Tot_Base_tl__bool)(Prims_list__bool *x0);

bool FStar_List_Tot_Base_index__bool(Prims_list__bool *l, Prims_int i);

bool FStar_Seq_Base_index__bool(Prims_list__bool *s, Prims_int i);

extern Prims_list__bool
*(*FStar_Seq_Base_slice__bool)(Prims_list__bool *x0, Prims_int x1, Prims_int x2);

Prims_list__bool *FStar_Seq_Properties_seq_to_list__bool(Prims_list__bool *s);

Prims_list__bool *FStar_BV_bv2list(Prims_pos n, Prims_list__bool *s);

extern Prims_list__bool
*(*FStar_BV_bvand)(Prims_pos x0, Prims_list__bool *x1, Prims_list__bool *x2);

extern Prims_list__bool
*(*FStar_BV_bvxor)(Prims_pos x0, Prims_list__bool *x1, Prims_list__bool *x2);

extern Prims_list__bool
*(*FStar_BV_bvor)(Prims_pos x0, Prims_list__bool *x1, Prims_list__bool *x2);

extern Prims_list__bool *(*FStar_BV_bvnot)(Prims_pos x0, Prims_list__bool *x1);

extern Prims_list__bool *(*FStar_BV_bvshl)(Prims_pos x0, Prims_list__bool *x1, Prims_int x2);

extern Prims_list__bool *(*FStar_BV_bvshr)(Prims_pos x0, Prims_list__bool *x1, Prims_int x2);

Prims_list__bool *FStar_BV_bv_zero(Prims_pos n);

bool FStar_BV_bvult(Prims_pos n, Prims_list__bool *a, Prims_list__bool *b);

Prims_list__bool *FStar_BV_bvadd(Prims_pos n, Prims_list__bool *a, Prims_list__bool *b);

Prims_list__bool *FStar_BV_bvsub(Prims_pos n, Prims_list__bool *a, Prims_list__bool *b);

Prims_list__bool *FStar_BV_bvdiv(Prims_pos n, Prims_list__bool *a, Prims_int b);

Prims_list__bool *FStar_BV_bvmod(Prims_pos n, Prims_list__bool *a, Prims_int b);

Prims_list__bool *FStar_BV_bvmul(Prims_pos n, Prims_list__bool *a, Prims_int b);


#define __FStar_BV_H_DEFINED
#endif
