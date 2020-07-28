/*
  Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
  Licensed under the Apache 2.0 License.
*/

#include <inttypes.h>
#include "kremlib.h"
#include "kremlin/internal/compat.h"
#include "kremlin/internal/target.h"

#ifndef __TestLib_H
#define __TestLib_H




extern void TestLib_touch(int32_t uu____7);

extern void TestLib_check(bool uu____15);

extern void TestLib_check8(int8_t uu____30, int8_t uu____31);

extern void TestLib_check16(int16_t uu____46, int16_t uu____47);

extern void TestLib_check32(int32_t uu____62, int32_t uu____63);

extern void TestLib_check64(int64_t uu____78, int64_t uu____79);

extern void TestLib_checku8(uint8_t uu____94, uint8_t uu____95);

extern void TestLib_checku16(uint16_t uu____110, uint16_t uu____111);

extern void TestLib_checku32(uint32_t uu____126, uint32_t uu____127);

extern void TestLib_checku64(uint64_t uu____142, uint64_t uu____143);

extern void
TestLib_compare_and_print(C_String_t uu____176, uint8_t *b1, uint8_t *b2, uint32_t l);

extern uint8_t *TestLib_unsafe_malloc(uint32_t l);

extern void TestLib_perr(uint32_t uu____203);

extern void TestLib_print_clock_diff(clock_t uu____218, clock_t uu____219);

KRML_DEPRECATED("p_null from TestLib; use LowStar.Buffer.null instead")

extern uint8_t *TestLib_uint8_p_null;

KRML_DEPRECATED("p_null from TestLib; use LowStar.Buffer.null instead")

extern uint32_t *TestLib_uint32_p_null;

KRML_DEPRECATED("p_null from TestLib; use LowStar.Buffer.null instead")

extern uint64_t *TestLib_uint64_p_null;

extern TestLib_cycles TestLib_cpucycles();

extern void
TestLib_print_cycles_per_round(
  TestLib_cycles uu____276,
  TestLib_cycles uu____277,
  uint32_t uu____278
);

#define __TestLib_H_DEFINED
#endif
