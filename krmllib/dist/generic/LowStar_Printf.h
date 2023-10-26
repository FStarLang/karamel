/*
  Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
  Licensed under the Apache 2.0 License.
*/


#ifndef __LowStar_Printf_H
#define __LowStar_Printf_H

#include <inttypes.h>
#include "krmllib.h"
#include "krml/internal/compat.h"
#include "krml/internal/target.h"

extern void LowStar_Printf_print_string(Prims_string uu___);

extern void LowStar_Printf_print_char(FStar_Char_char uu___);

extern void LowStar_Printf_print_u8(uint8_t uu___);

extern void LowStar_Printf_print_u16(uint16_t uu___);

extern void LowStar_Printf_print_u32(uint32_t uu___);

extern void LowStar_Printf_print_u64(uint64_t uu___);

extern void LowStar_Printf_print_i8(int8_t uu___);

extern void LowStar_Printf_print_i16(int16_t uu___);

extern void LowStar_Printf_print_i32(int32_t uu___);

extern void LowStar_Printf_print_i64(int64_t uu___);

extern void LowStar_Printf_print_bool(bool uu___);

extern void LowStar_Printf_print_lmbuffer_bool(uint32_t l, bool *b);

extern void LowStar_Printf_print_lmbuffer_char(uint32_t l, FStar_Char_char *b);

extern void LowStar_Printf_print_lmbuffer_string(uint32_t l, Prims_string *b);

extern void LowStar_Printf_print_lmbuffer_u8(uint32_t l, uint8_t *b);

extern void LowStar_Printf_print_lmbuffer_u16(uint32_t l, uint16_t *b);

extern void LowStar_Printf_print_lmbuffer_u32(uint32_t l, uint32_t *b);

extern void LowStar_Printf_print_lmbuffer_u64(uint32_t l, uint64_t *b);

extern void LowStar_Printf_print_lmbuffer_i8(uint32_t l, int8_t *b);

extern void LowStar_Printf_print_lmbuffer_i16(uint32_t l, int16_t *b);

extern void LowStar_Printf_print_lmbuffer_i32(uint32_t l, int32_t *b);

extern void LowStar_Printf_print_lmbuffer_i64(uint32_t l, int64_t *b);

extern void LowStar_Printf_test(uint64_t m, uint32_t l, bool *x);

typedef struct K___krml_checked_int_t_krml_checked_int_t_s
{
  krml_checked_int_t fst;
  krml_checked_int_t snd;
}
K___krml_checked_int_t_krml_checked_int_t;

extern void
LowStar_Printf_test2(
  K___krml_checked_int_t_krml_checked_int_t x,
  void (*print_pair)(K___krml_checked_int_t_krml_checked_int_t x0)
);

extern void LowStar_Printf_test3(uint64_t m, uint32_t l, bool *x);


#define __LowStar_Printf_H_DEFINED
#endif
