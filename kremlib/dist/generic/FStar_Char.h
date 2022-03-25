/*
  Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
  Licensed under the Apache 2.0 License.
*/


#ifndef __FStar_Char_H
#define __FStar_Char_H




#include <inttypes.h>
#include "kremlib.h"
#include "kremlin/internal/compat.h"
#include "kremlin/internal/target.h"
typedef uint32_t FStar_Char_char_code;

extern uint32_t FStar_Char_u32_of_char(FStar_Char_char uu___);

extern FStar_Char_char FStar_Char_char_of_u32(uint32_t uu___);

extern Prims_int FStar_Char_int_of_char(FStar_Char_char c);

extern FStar_Char_char FStar_Char_char_of_int(Prims_int i);

extern FStar_Char_char FStar_Char_lowercase(FStar_Char_char uu___);

extern FStar_Char_char FStar_Char_uppercase(FStar_Char_char uu___);


#define __FStar_Char_H_DEFINED
#endif
