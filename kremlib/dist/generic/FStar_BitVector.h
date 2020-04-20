/*
  Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
  Licensed under the Apache 2.0 License.
*/

#include <inttypes.h>
#include "kremlib.h"
#include "kremlin/internal/compat.h"
#include "kremlin/internal/target.h"

#ifndef __FStar_BitVector_H
#define __FStar_BitVector_H




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

typedef Prims_list__bool *FStar_Seq_Base_seq__bool;

extern Prims_list__bool *FStar_BitVector_zero_vec(Prims_pos n);

extern Prims_list__bool *FStar_BitVector_elem_vec(Prims_pos n, Prims_int i);

extern Prims_list__bool *FStar_BitVector_ones_vec(Prims_pos n);

extern Prims_list__bool
*FStar_BitVector_logand_vec(Prims_pos n, Prims_list__bool *a, Prims_list__bool *b);

extern Prims_list__bool
*FStar_BitVector_logxor_vec(Prims_pos n, Prims_list__bool *a, Prims_list__bool *b);

extern Prims_list__bool
*FStar_BitVector_logor_vec(Prims_pos n, Prims_list__bool *a, Prims_list__bool *b);

extern Prims_list__bool *FStar_BitVector_lognot_vec(Prims_pos n, Prims_list__bool *a);

extern Prims_list__bool
*FStar_BitVector_shift_left_vec(Prims_pos n, Prims_list__bool *a, Prims_int s);

extern Prims_list__bool
*FStar_BitVector_shift_right_vec(Prims_pos n, Prims_list__bool *a, Prims_int s);

extern Prims_list__bool
*FStar_BitVector_shift_arithmetic_right_vec(Prims_pos n, Prims_list__bool *a, Prims_int s);

#define __FStar_BitVector_H_DEFINED
#endif
