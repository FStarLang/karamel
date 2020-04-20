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




extern void TestLib_touch(int32_t uu____12);

extern void TestLib_check(bool uu____28);

extern void TestLib_check8(int8_t uu____52, int8_t uu____53);

extern void TestLib_check16(int16_t uu____78, int16_t uu____79);

extern void TestLib_check32(int32_t uu____104, int32_t uu____105);

extern void TestLib_check64(int64_t uu____130, int64_t uu____131);

extern void TestLib_checku8(uint8_t uu____156, uint8_t uu____157);

extern void TestLib_checku16(uint16_t uu____182, uint16_t uu____183);

extern void TestLib_checku32(uint32_t uu____208, uint32_t uu____209);

extern void TestLib_checku64(uint64_t uu____234, uint64_t uu____235);

extern void
TestLib_compare_and_print(C_String_t uu____279, uint8_t *b1, uint8_t *b2, uint32_t l);

extern uint8_t *TestLib_unsafe_malloc(uint32_t l);

extern void TestLib_perr(uint32_t uu____326);

extern void TestLib_print_clock_diff(clock_t uu____348, clock_t uu____349);

KRML_DEPRECATED("p_null from TestLib; use LowStar.Buffer.null instead")

extern uint8_t *TestLib_uint8_p_null;

KRML_DEPRECATED("p_null from TestLib; use LowStar.Buffer.null instead")

extern uint32_t *TestLib_uint32_p_null;

KRML_DEPRECATED("p_null from TestLib; use LowStar.Buffer.null instead")

extern uint64_t *TestLib_uint64_p_null;

extern TestLib_cycles TestLib_cpucycles();

extern void
TestLib_print_cycles_per_round(
  TestLib_cycles uu____434,
  TestLib_cycles uu____435,
  uint32_t uu____436
);

#define __TestLib_H_DEFINED
#endif
