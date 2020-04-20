/*
  Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
  Licensed under the Apache 2.0 License.
*/

#include <inttypes.h>
#include "kremlib.h"
#include "kremlin/internal/compat.h"
#include "kremlin/internal/target.h"

#ifndef __C_Loops_H
#define __C_Loops_H




extern void C_Loops_for_(uint32_t start, uint32_t finish, void (*inv)(uint32_t x0));

extern void C_Loops_for64(uint64_t start, uint64_t finish, void (*inv)(uint64_t x0));

extern void C_Loops_reverse_for(uint32_t start, uint32_t finish, void (*inv)(uint32_t x0));

typedef struct K___uint32_t_bool_s
{
  uint32_t fst;
  bool snd;
}
K___uint32_t_bool;

extern K___uint32_t_bool
C_Loops_interruptible_for(uint32_t start, uint32_t finish, bool (*inv)(uint32_t x0));

extern K___uint32_t_bool
C_Loops_interruptible_reverse_for(uint32_t start, uint32_t finish, bool (*inv)(uint32_t x0));

#define __C_Loops_H_DEFINED
#endif
