/*
  Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
  Licensed under the Apache 2.0 License.
*/

#include <inttypes.h>
#include "kremlib.h"
#include "kremlin/internal/compat.h"
#include "kremlin/internal/target.h"

#ifndef __C_Endianness_H
#define __C_Endianness_H

#include "FStar_UInt128.h"


KRML_DEPRECATED("LowStar.Endianness.load128_le")

static inline FStar_UInt128_uint128 load128_le0(uint8_t *b);

KRML_DEPRECATED("LowStar.Endianness.store128_le")

static inline void store128_le0(uint8_t *b, FStar_UInt128_uint128 z);

KRML_DEPRECATED("LowStar.Endianness.load128_be")

static inline FStar_UInt128_uint128 load128_be0(uint8_t *b);

KRML_DEPRECATED("LowStar.Endianness.store128_be")

static inline void store128_be0(uint8_t *b, FStar_UInt128_uint128 z);

KRML_DEPRECATED("LowStar.Endianness.index_32_be")

static inline uint32_t index_32_be(uint8_t *b, uint32_t i);

KRML_DEPRECATED("LowStar.Endianness.index_32_le")

static inline uint32_t index_32_le(uint8_t *b, uint32_t i);

KRML_DEPRECATED("LowStar.Endianness.index_64_be")

static inline uint64_t index_64_be(uint8_t *b, uint32_t i);

KRML_DEPRECATED("LowStar.Endianness.index_64_le")

static inline uint64_t index_64_le(uint8_t *b, uint32_t i);

KRML_DEPRECATED("LowStar.Endianness.upd_32_be")

static inline void upd_32_be(uint8_t *b, uint32_t i, uint32_t v1);

#define __C_Endianness_H_DEFINED
#endif
