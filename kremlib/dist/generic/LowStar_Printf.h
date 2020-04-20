/*
  Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
  Licensed under the Apache 2.0 License.
*/

#include <inttypes.h>
#include "kremlib.h"
#include "kremlin/internal/compat.h"
#include "kremlin/internal/target.h"

#ifndef __LowStar_Printf_H
#define __LowStar_Printf_H




extern void LowStar_Printf_print_string(Prims_string uu____92);

extern void LowStar_Printf_print_char(FStar_Char_char uu____104);

extern void LowStar_Printf_print_u8(uint8_t uu____116);

extern void LowStar_Printf_print_u16(uint16_t uu____128);

extern void LowStar_Printf_print_u32(uint32_t uu____140);

extern void LowStar_Printf_print_u64(uint64_t uu____152);

extern void LowStar_Printf_print_i8(int8_t uu____164);

extern void LowStar_Printf_print_i16(int16_t uu____176);

extern void LowStar_Printf_print_i32(int32_t uu____188);

extern void LowStar_Printf_print_i64(int64_t uu____200);

extern void LowStar_Printf_print_bool(bool uu____212);

extern void LowStar_Printf_print_lmbuffer_bool(uint32_t l, bool *r);

extern void LowStar_Printf_print_lmbuffer_char(uint32_t l, FStar_Char_char *r);

extern void LowStar_Printf_print_lmbuffer_string(uint32_t l, Prims_string *r);

extern void LowStar_Printf_print_lmbuffer_u8(uint32_t l, uint8_t *r);

extern void LowStar_Printf_print_lmbuffer_u16(uint32_t l, uint16_t *r);

extern void LowStar_Printf_print_lmbuffer_u32(uint32_t l, uint32_t *r);

extern void LowStar_Printf_print_lmbuffer_u64(uint32_t l, uint64_t *r);

extern void LowStar_Printf_print_lmbuffer_i8(uint32_t l, int8_t *r);

extern void LowStar_Printf_print_lmbuffer_i16(uint32_t l, int16_t *r);

extern void LowStar_Printf_print_lmbuffer_i32(uint32_t l, int32_t *r);

extern void LowStar_Printf_print_lmbuffer_i64(uint32_t l, int64_t *r);

extern void LowStar_Printf_test(uint64_t m, uint32_t l, bool *r);

typedef struct K___Prims_int_Prims_int_s
{
  Prims_int fst;
  Prims_int snd;
}
K___Prims_int_Prims_int;

extern void
LowStar_Printf_test2(K___Prims_int_Prims_int x, void (*print_pair)(K___Prims_int_Prims_int x0));

extern void LowStar_Printf_test3(uint64_t m, uint32_t l, bool *r);

#define __LowStar_Printf_H_DEFINED
#endif
