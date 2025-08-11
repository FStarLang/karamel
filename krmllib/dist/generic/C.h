/*
  Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
  Licensed under the Apache 2.0 and MIT Licenses.
*/


#ifndef KRML_HEADER_C_H
#define KRML_HEADER_C_H

#include <inttypes.h>
#include "krmllib.h"
#include "krml/internal/compat.h"
#include "krml/internal/target.h"

extern void portable_exit(int32_t uu___);

extern char char_of_uint8(uint8_t uu___);

extern uint8_t uint8_of_char(char uu___);

extern bool uu___is_EXIT_SUCCESS(exit_code projectee);

extern bool uu___is_EXIT_FAILURE(exit_code projectee);

extern void print_bytes(uint8_t *b, uint32_t len);


#define KRML_HEADER_C_H_DEFINED
#endif /* KRML_HEADER_C_H */
