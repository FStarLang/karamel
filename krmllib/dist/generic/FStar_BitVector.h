/*
  Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
  Licensed under the Apache 2.0 and MIT Licenses.
*/


#ifndef KRML_HEADER_FStar_BitVector_H
#define KRML_HEADER_FStar_BitVector_H

#include <inttypes.h>
#include "krmllib.h"
#include "krml/internal/compat.h"
#include "krml/internal/target.h"

typedef struct Prims_list__bool_s Prims_list__bool;

#define Prims_Nil 0
#define Prims_Cons 1

typedef uint8_t Prims_list__bool_tags;

typedef struct Prims_list__bool_s
{
  Prims_list__bool_tags tag;
  bool hd;
  Prims_list__bool *tl;
}
Prims_list__bool;

typedef Prims_list__bool *FStar_BitVector_bv_t;

extern Prims_list__bool *FStar_BitVector_zero_vec(krml_checked_int_t n);

extern Prims_list__bool *FStar_BitVector_elem_vec(krml_checked_int_t n, krml_checked_int_t i);

extern Prims_list__bool *FStar_BitVector_ones_vec(krml_checked_int_t n);

extern Prims_list__bool
*FStar_BitVector_logand_vec(krml_checked_int_t n, Prims_list__bool *a, Prims_list__bool *b);

extern Prims_list__bool
*FStar_BitVector_logxor_vec(krml_checked_int_t n, Prims_list__bool *a, Prims_list__bool *b);

extern Prims_list__bool
*FStar_BitVector_logor_vec(krml_checked_int_t n, Prims_list__bool *a, Prims_list__bool *b);

extern Prims_list__bool *FStar_BitVector_lognot_vec(krml_checked_int_t n, Prims_list__bool *a);

typedef void *FStar_BitVector_is_subset_vec;

typedef void *FStar_BitVector_is_superset_vec;

extern Prims_list__bool
*FStar_BitVector_shift_left_vec(
  krml_checked_int_t n,
  Prims_list__bool *a,
  krml_checked_int_t s
);

extern Prims_list__bool
*FStar_BitVector_shift_right_vec(
  krml_checked_int_t n,
  Prims_list__bool *a,
  krml_checked_int_t s
);

extern Prims_list__bool
*FStar_BitVector_shift_arithmetic_right_vec(
  krml_checked_int_t n,
  Prims_list__bool *a,
  krml_checked_int_t s
);


#define KRML_HEADER_FStar_BitVector_H_DEFINED
#endif /* KRML_HEADER_FStar_BitVector_H */
