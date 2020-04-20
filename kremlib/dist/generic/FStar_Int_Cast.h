/*
  Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
  Licensed under the Apache 2.0 License.
*/

#include <inttypes.h>
#include "kremlib.h"
#include "kremlin/internal/compat.h"
#include "kremlin/internal/target.h"

#ifndef __FStar_Int_Cast_H
#define __FStar_Int_Cast_H




extern uint64_t FStar_Int_Cast_uint8_to_uint64(uint8_t a);

extern uint32_t FStar_Int_Cast_uint8_to_uint32(uint8_t x);

extern uint16_t FStar_Int_Cast_uint8_to_uint16(uint8_t x);

extern uint64_t FStar_Int_Cast_uint16_to_uint64(uint16_t x);

extern uint32_t FStar_Int_Cast_uint16_to_uint32(uint16_t x);

extern uint8_t FStar_Int_Cast_uint16_to_uint8(uint16_t x);

extern uint64_t FStar_Int_Cast_uint32_to_uint64(uint32_t x);

extern uint16_t FStar_Int_Cast_uint32_to_uint16(uint32_t x);

extern uint8_t FStar_Int_Cast_uint32_to_uint8(uint32_t x);

extern uint32_t FStar_Int_Cast_uint64_to_uint32(uint64_t x);

extern uint16_t FStar_Int_Cast_uint64_to_uint16(uint64_t x);

extern uint8_t FStar_Int_Cast_uint64_to_uint8(uint64_t x);

extern int64_t FStar_Int_Cast_int8_to_int64(int8_t x);

extern int32_t FStar_Int_Cast_int8_to_int32(int8_t x);

extern int16_t FStar_Int_Cast_int8_to_int16(int8_t x);

extern int64_t FStar_Int_Cast_int16_to_int64(int16_t x);

extern int32_t FStar_Int_Cast_int16_to_int32(int16_t x);

KRML_DEPRECATED("with care; in C the result is implementation-defined when not representable")

KRML_DEPRECATED("with care; in C the result is implementation-defined when not representable")

extern int8_t FStar_Int_Cast_int16_to_int8(int16_t x);

extern int64_t FStar_Int_Cast_int32_to_int64(int32_t x);

KRML_DEPRECATED("with care; in C the result is implementation-defined when not representable")

KRML_DEPRECATED("with care; in C the result is implementation-defined when not representable")

extern int16_t FStar_Int_Cast_int32_to_int16(int32_t x);

KRML_DEPRECATED("with care; in C the result is implementation-defined when not representable")

KRML_DEPRECATED("with care; in C the result is implementation-defined when not representable")

extern int8_t FStar_Int_Cast_int32_to_int8(int32_t x);

KRML_DEPRECATED("with care; in C the result is implementation-defined when not representable")

KRML_DEPRECATED("with care; in C the result is implementation-defined when not representable")

extern int32_t FStar_Int_Cast_int64_to_int32(int64_t x);

KRML_DEPRECATED("with care; in C the result is implementation-defined when not representable")

KRML_DEPRECATED("with care; in C the result is implementation-defined when not representable")

extern int16_t FStar_Int_Cast_int64_to_int16(int64_t x);

KRML_DEPRECATED("with care; in C the result is implementation-defined when not representable")

KRML_DEPRECATED("with care; in C the result is implementation-defined when not representable")

extern int8_t FStar_Int_Cast_int64_to_int8(int64_t x);

extern int64_t FStar_Int_Cast_uint8_to_int64(uint8_t x);

extern int32_t FStar_Int_Cast_uint8_to_int32(uint8_t x);

extern int16_t FStar_Int_Cast_uint8_to_int16(uint8_t x);

KRML_DEPRECATED("with care; in C the result is implementation-defined when not representable")

KRML_DEPRECATED("with care; in C the result is implementation-defined when not representable")

extern int8_t FStar_Int_Cast_uint8_to_int8(uint8_t x);

extern int64_t FStar_Int_Cast_uint16_to_int64(uint16_t x);

extern int32_t FStar_Int_Cast_uint16_to_int32(uint16_t x);

KRML_DEPRECATED("with care; in C the result is implementation-defined when not representable")

KRML_DEPRECATED("with care; in C the result is implementation-defined when not representable")

extern int16_t FStar_Int_Cast_uint16_to_int16(uint16_t x);

KRML_DEPRECATED("with care; in C the result is implementation-defined when not representable")

KRML_DEPRECATED("with care; in C the result is implementation-defined when not representable")

extern int8_t FStar_Int_Cast_uint16_to_int8(uint16_t x);

extern int64_t FStar_Int_Cast_uint32_to_int64(uint32_t x);

KRML_DEPRECATED("with care; in C the result is implementation-defined when not representable")

KRML_DEPRECATED("with care; in C the result is implementation-defined when not representable")

extern int32_t FStar_Int_Cast_uint32_to_int32(uint32_t x);

KRML_DEPRECATED("with care; in C the result is implementation-defined when not representable")

KRML_DEPRECATED("with care; in C the result is implementation-defined when not representable")

extern int16_t FStar_Int_Cast_uint32_to_int16(uint32_t x);

KRML_DEPRECATED("with care; in C the result is implementation-defined when not representable")

KRML_DEPRECATED("with care; in C the result is implementation-defined when not representable")

extern int8_t FStar_Int_Cast_uint32_to_int8(uint32_t x);

KRML_DEPRECATED("with care; in C the result is implementation-defined when not representable")

KRML_DEPRECATED("with care; in C the result is implementation-defined when not representable")

extern int64_t FStar_Int_Cast_uint64_to_int64(uint64_t x);

KRML_DEPRECATED("with care; in C the result is implementation-defined when not representable")

KRML_DEPRECATED("with care; in C the result is implementation-defined when not representable")

extern int32_t FStar_Int_Cast_uint64_to_int32(uint64_t x);

KRML_DEPRECATED("with care; in C the result is implementation-defined when not representable")

KRML_DEPRECATED("with care; in C the result is implementation-defined when not representable")

extern int16_t FStar_Int_Cast_uint64_to_int16(uint64_t x);

KRML_DEPRECATED("with care; in C the result is implementation-defined when not representable")

KRML_DEPRECATED("with care; in C the result is implementation-defined when not representable")

extern int8_t FStar_Int_Cast_uint64_to_int8(uint64_t x);

extern uint64_t FStar_Int_Cast_int8_to_uint64(int8_t x);

extern uint32_t FStar_Int_Cast_int8_to_uint32(int8_t x);

extern uint16_t FStar_Int_Cast_int8_to_uint16(int8_t x);

extern uint8_t FStar_Int_Cast_int8_to_uint8(int8_t x);

extern uint64_t FStar_Int_Cast_int16_to_uint64(int16_t x);

extern uint32_t FStar_Int_Cast_int16_to_uint32(int16_t x);

extern uint16_t FStar_Int_Cast_int16_to_uint16(int16_t x);

extern uint8_t FStar_Int_Cast_int16_to_uint8(int16_t x);

extern uint64_t FStar_Int_Cast_int32_to_uint64(int32_t x);

extern uint32_t FStar_Int_Cast_int32_to_uint32(int32_t x);

extern uint16_t FStar_Int_Cast_int32_to_uint16(int32_t x);

extern uint8_t FStar_Int_Cast_int32_to_uint8(int32_t x);

extern uint64_t FStar_Int_Cast_int64_to_uint64(int64_t x);

extern uint32_t FStar_Int_Cast_int64_to_uint32(int64_t x);

extern uint16_t FStar_Int_Cast_int64_to_uint16(int64_t x);

extern uint8_t FStar_Int_Cast_int64_to_uint8(int64_t x);

#define __FStar_Int_Cast_H_DEFINED
#endif
