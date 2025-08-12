/*
  Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
  Licensed under the Apache 2.0 and MIT Licenses.
*/


#ifndef TestLib_H
#define TestLib_H

#include <inttypes.h>
#include "krmllib.h"
#include "krml/internal/compat.h"
#include "krml/internal/target.h"

extern void TestLib_touch(int32_t uu___);

extern void TestLib_check(bool uu___);

extern void TestLib_check8(int8_t uu___, int8_t uu___1);

extern void TestLib_check16(int16_t uu___, int16_t uu___1);

extern void TestLib_check32(int32_t uu___, int32_t uu___1);

extern void TestLib_check64(int64_t uu___, int64_t uu___1);

extern void TestLib_checku8(uint8_t uu___, uint8_t uu___1);

extern void TestLib_checku16(uint16_t uu___, uint16_t uu___1);

extern void TestLib_checku32(uint32_t uu___, uint32_t uu___1);

extern void TestLib_checku64(uint64_t uu___, uint64_t uu___1);

extern void
TestLib_compare_and_print(Prims_string uu___, uint8_t *b1, uint8_t *b2, uint32_t l);

extern uint8_t *TestLib_unsafe_malloc(uint32_t l);

extern void TestLib_perr(uint32_t uu___);

extern void TestLib_print_clock_diff(clock_t uu___, clock_t uu___1);

KRML_DEPRECATED("p_null from TestLib; use LowStar.Buffer.null instead")

extern uint8_t *TestLib_uint8_p_null;

KRML_DEPRECATED("p_null from TestLib; use LowStar.Buffer.null instead")

extern uint32_t *TestLib_uint32_p_null;

KRML_DEPRECATED("p_null from TestLib; use LowStar.Buffer.null instead")

extern uint64_t *TestLib_uint64_p_null;

extern TestLib_cycles TestLib_cpucycles(void);

extern void
TestLib_print_cycles_per_round(TestLib_cycles uu___, TestLib_cycles uu___1, uint32_t uu___2);


#define TestLib_H_DEFINED
#endif /* TestLib_H */
