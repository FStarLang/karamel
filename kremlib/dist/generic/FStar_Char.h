/*
  Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
  Licensed under the Apache 2.0 License.
*/

#include <inttypes.h>
#include "kremlib.h"
#include "kremlin/internal/compat.h"
#include "kremlin/internal/target.h"

#ifndef __FStar_Char_H
#define __FStar_Char_H




typedef uint32_t FStar_Char_char_code;

extern uint32_t FStar_Char_u32_of_char(FStar_Char_char uu____10);

extern FStar_Char_char FStar_Char_char_of_u32(uint32_t uu____22);

extern Prims_int FStar_Char_int_of_char(FStar_Char_char c);

extern FStar_Char_char FStar_Char_char_of_int(Prims_int i);

extern FStar_Char_char FStar_Char_lowercase(FStar_Char_char uu____52);

extern FStar_Char_char FStar_Char_uppercase(FStar_Char_char uu____66);

#define __FStar_Char_H_DEFINED
#endif
