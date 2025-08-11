/*
  Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
  Licensed under the Apache 2.0 and MIT Licenses.
*/


#ifndef KRML_HEADER_LowStar_Endianness_H
#define KRML_HEADER_LowStar_Endianness_H

#include <inttypes.h>
#include "krmllib.h"
#include "krml/internal/compat.h"
#include "krml/internal/target.h"

static inline void store128_le(uint8_t *x0, FStar_UInt128_uint128 x1);

static inline FStar_UInt128_uint128 load128_le(uint8_t *x0);

static inline void store128_be(uint8_t *x0, FStar_UInt128_uint128 x1);

static inline FStar_UInt128_uint128 load128_be(uint8_t *x0);


#define KRML_HEADER_LowStar_Endianness_H_DEFINED
#endif /* KRML_HEADER_LowStar_Endianness_H */
