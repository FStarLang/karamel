/*
  Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
  Licensed under the Apache 2.0 and MIT Licenses.
*/


#ifndef KRML_HEADER_FStar_Char_H
#define KRML_HEADER_FStar_Char_H

#include <inttypes.h>
#include "krmllib.h"
#include "krml/internal/compat.h"
#include "krml/internal/target.h"

typedef uint32_t FStar_Char_char_code;

extern uint32_t FStar_Char_u32_of_char(FStar_Char_char uu___);

extern FStar_Char_char FStar_Char_char_of_u32(uint32_t uu___);

extern krml_checked_int_t FStar_Char_int_of_char(FStar_Char_char c);

extern FStar_Char_char FStar_Char_char_of_int(krml_checked_int_t i);

extern FStar_Char_char FStar_Char_lowercase(FStar_Char_char uu___);

extern FStar_Char_char FStar_Char_uppercase(FStar_Char_char uu___);


#define KRML_HEADER_FStar_Char_H_DEFINED
#endif /* KRML_HEADER_FStar_Char_H */
