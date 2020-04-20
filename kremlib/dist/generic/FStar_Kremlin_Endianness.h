/*
  Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
  Licensed under the Apache 2.0 License.
*/

#include <inttypes.h>
#include "kremlib.h"
#include "kremlin/internal/compat.h"
#include "kremlin/internal/target.h"

#ifndef __FStar_Kremlin_Endianness_H
#define __FStar_Kremlin_Endianness_H

#include "FStar_BitVector.h"


typedef struct Prims_list__uint8_t_s Prims_list__uint8_t;

typedef struct Prims_list__uint8_t_s
{
  Prims_list__bool_tags tag;
  uint8_t hd;
  Prims_list__uint8_t *tl;
}
Prims_list__uint8_t;

typedef Prims_list__uint8_t *FStar_Seq_Base_seq__uint8_t;

typedef Prims_list__uint8_t *FStar_Kremlin_Endianness_bytes;

KRML_DEPRECATED("FStar.Endianness.le_to_n")

extern Prims_int FStar_Kremlin_Endianness_le_to_n(Prims_list__uint8_t *b);

KRML_DEPRECATED("FStar.Endianness.be_to_n")

extern Prims_int FStar_Kremlin_Endianness_be_to_n(Prims_list__uint8_t *b);

KRML_DEPRECATED("FStar.Endianness.n_to_le")

extern Prims_list__uint8_t *FStar_Kremlin_Endianness_n_to_le(uint32_t len, Prims_int n1);

KRML_DEPRECATED("FStar.Endianness.n_to_be")

extern Prims_list__uint8_t *FStar_Kremlin_Endianness_n_to_be(uint32_t len, Prims_int n1);

KRML_DEPRECATED("FStar.Endianness.uint32_of_le")

extern uint32_t FStar_Kremlin_Endianness_uint32_of_le(Prims_list__uint8_t *b);

KRML_DEPRECATED("FStar.Endianness.le_of_uint32")

extern Prims_list__uint8_t *FStar_Kremlin_Endianness_le_of_uint32(uint32_t x);

KRML_DEPRECATED("FStar.Endianness.uint32_of_be")

extern uint32_t FStar_Kremlin_Endianness_uint32_of_be(Prims_list__uint8_t *b);

KRML_DEPRECATED("FStar.Endianness.be_of_uint32")

extern Prims_list__uint8_t *FStar_Kremlin_Endianness_be_of_uint32(uint32_t x);

KRML_DEPRECATED("FStar.Endianness.uint64_of_le")

extern uint64_t FStar_Kremlin_Endianness_uint64_of_le(Prims_list__uint8_t *b);

KRML_DEPRECATED("FStar.Endianness.le_of_uint64")

extern Prims_list__uint8_t *FStar_Kremlin_Endianness_le_of_uint64(uint64_t x);

KRML_DEPRECATED("FStar.Endianness.uint64_of_be")

extern uint64_t FStar_Kremlin_Endianness_uint64_of_be(Prims_list__uint8_t *b);

KRML_DEPRECATED("FStar.Endianness.be_of_uint64")

extern Prims_list__uint8_t *FStar_Kremlin_Endianness_be_of_uint64(uint64_t x);

typedef struct Prims_list__uint32_t_s Prims_list__uint32_t;

typedef struct Prims_list__uint32_t_s
{
  Prims_list__bool_tags tag;
  uint32_t hd;
  Prims_list__uint32_t *tl;
}
Prims_list__uint32_t;

typedef Prims_list__uint32_t *FStar_Seq_Base_seq__uint32_t;

KRML_DEPRECATED("FStar.Endianness.seq_uint32_of_le")

extern Prims_list__uint32_t
*FStar_Kremlin_Endianness_seq_uint32_of_le(Prims_int l, Prims_list__uint8_t *b);

KRML_DEPRECATED("FStar.Endianness.le_of_seq_uint32")

extern Prims_list__uint8_t *FStar_Kremlin_Endianness_le_of_seq_uint32(Prims_list__uint32_t *s);

KRML_DEPRECATED("FStar.Endianness.seq_uint32_of_be")

extern Prims_list__uint32_t
*FStar_Kremlin_Endianness_seq_uint32_of_be(Prims_int l, Prims_list__uint8_t *b);

KRML_DEPRECATED("FStar.Endianness.be_of_seq_uint32")

extern Prims_list__uint8_t *FStar_Kremlin_Endianness_be_of_seq_uint32(Prims_list__uint32_t *s);

typedef struct Prims_list__uint64_t_s Prims_list__uint64_t;

typedef struct Prims_list__uint64_t_s
{
  Prims_list__bool_tags tag;
  uint64_t hd;
  Prims_list__uint64_t *tl;
}
Prims_list__uint64_t;

typedef Prims_list__uint64_t *FStar_Seq_Base_seq__uint64_t;

KRML_DEPRECATED("FStar.Endianness.seq_uint64_of_le")

extern Prims_list__uint64_t
*FStar_Kremlin_Endianness_seq_uint64_of_le(Prims_int l, Prims_list__uint8_t *b);

KRML_DEPRECATED("FStar.Endianness.le_of_seq_uint64")

extern Prims_list__uint8_t *FStar_Kremlin_Endianness_le_of_seq_uint64(Prims_list__uint64_t *s);

KRML_DEPRECATED("FStar.Endianness.seq_uint64_of_be")

extern Prims_list__uint64_t
*FStar_Kremlin_Endianness_seq_uint64_of_be(Prims_int l, Prims_list__uint8_t *b);

KRML_DEPRECATED("FStar.Endianness.be_of_seq_uint64")

extern Prims_list__uint8_t *FStar_Kremlin_Endianness_be_of_seq_uint64(Prims_list__uint64_t *s);

#define __FStar_Kremlin_Endianness_H_DEFINED
#endif
