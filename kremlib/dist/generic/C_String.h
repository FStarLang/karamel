/*
  Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
  Licensed under the Apache 2.0 License.
*/

#include <inttypes.h>
#include "kremlib.h"
#include "kremlin/internal/compat.h"
#include "kremlin/internal/target.h"

#ifndef __C_String_H
#define __C_String_H

#include "FStar_BitVector.h"


extern bool C_String_uu___is_S(C_String_t projectee);

typedef struct Prims_list__C_char_s Prims_list__C_char;

typedef struct Prims_list__C_char_s
{
  Prims_list__bool_tags tag;
  char hd;
  Prims_list__C_char *tl;
}
Prims_list__C_char;

typedef Prims_list__C_char *FStar_Seq_Base_seq__C_char;

extern Prims_list__C_char *C_String___proj__S__item__s(C_String_t projectee);

extern void C_String_print(C_String_t uu____143);

extern uint32_t C_String_strlen(C_String_t uu____151);

extern void C_String_memcpy(uint8_t *uu____179, C_String_t uu____180, uint32_t uu____181);

#define __C_String_H_DEFINED
#endif
