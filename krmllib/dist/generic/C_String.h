/*
  Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
  Licensed under the Apache 2.0 and MIT Licenses.
*/


#ifndef KRML_HEADER_C_String_H
#define KRML_HEADER_C_String_H

#include <inttypes.h>
#include "krmllib.h"
#include "krml/internal/compat.h"
#include "krml/internal/target.h"

typedef void *C_String_zero_free;

typedef void *C_String_well_formed;

extern void C_String_print(Prims_string uu___);

extern uint32_t C_String_strlen(Prims_string uu___);

extern void C_String_memcpy(uint8_t *uu___, Prims_string uu___1, uint32_t uu___2);


#define KRML_HEADER_C_String_H_DEFINED
#endif /* KRML_HEADER_C_String_H */
