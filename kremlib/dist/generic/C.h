/*
  Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
  Licensed under the Apache 2.0 License.
*/

#include <inttypes.h>
#include "kremlib.h"
#include "kremlin/internal/compat.h"
#include "kremlin/internal/target.h"

#ifndef __C_H
#define __C_H




extern void portable_exit(int32_t uu____60);

extern char char_of_uint8(uint8_t uu____94);

extern uint8_t uint8_of_char(char uu____106);

extern bool uu___is_EXIT_SUCCESS(exit_code projectee);

extern bool uu___is_EXIT_FAILURE(exit_code projectee);

extern void print_bytes(uint8_t *b, uint32_t len);

#define __C_H_DEFINED
#endif
