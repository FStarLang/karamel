/*
  Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
  Licensed under the Apache 2.0 License.
*/


#ifndef __C_String_H
#define __C_String_H




#include <inttypes.h>
#include "krmllib.h"
#include "krml/internal/compat.h"
#include "krml/internal/target.h"
extern void C_String_print(C_String_t uu___);

extern uint32_t C_String_strlen(C_String_t uu___);

extern void C_String_memcpy(uint8_t *uu___, C_String_t uu___1, uint32_t uu___2);


#define __C_String_H_DEFINED
#endif
