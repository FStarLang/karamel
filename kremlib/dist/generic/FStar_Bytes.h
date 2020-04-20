/*
  Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
  Licensed under the Apache 2.0 License.
*/

#include <inttypes.h>
#include "kremlib.h"
#include "kremlin/internal/compat.h"
#include "kremlin/internal/target.h"

#ifndef __FStar_Bytes_H
#define __FStar_Bytes_H




typedef uint8_t FStar_Bytes_u8;

typedef uint16_t FStar_Bytes_u16;

typedef uint32_t FStar_Bytes_u32;

typedef uint8_t FStar_Bytes_byte;

extern uint32_t FStar_Bytes_len(FStar_Bytes_bytes uu____18);

extern Prims_int FStar_Bytes_length(FStar_Bytes_bytes b);

extern FStar_Bytes_bytes FStar_Bytes_empty_bytes;

extern uint8_t FStar_Bytes_get(FStar_Bytes_bytes b, uint32_t pos);

extern uint8_t FStar_Bytes_op_String_Access(FStar_Bytes_bytes x0, uint32_t x1);

extern uint8_t FStar_Bytes_index(FStar_Bytes_bytes b, Prims_int i);

extern FStar_Bytes_bytes FStar_Bytes_create(uint32_t len1, uint8_t v1);

extern FStar_Bytes_bytes FStar_Bytes_create_(Prims_int n1, uint8_t v1);

extern FStar_Bytes_bytes FStar_Bytes_init(uint32_t len1, uint8_t (*f)(uint32_t x0));

extern FStar_Bytes_bytes FStar_Bytes_abyte(uint8_t b);

typedef struct K___uint8_t_uint8_t_s
{
  uint8_t fst;
  uint8_t snd;
}
K___uint8_t_uint8_t;

extern FStar_Bytes_bytes FStar_Bytes_twobytes(K___uint8_t_uint8_t b);

extern FStar_Bytes_bytes FStar_Bytes_append(FStar_Bytes_bytes b1, FStar_Bytes_bytes b2);

extern FStar_Bytes_bytes FStar_Bytes_op_At_Bar(FStar_Bytes_bytes x0, FStar_Bytes_bytes x1);

extern FStar_Bytes_bytes FStar_Bytes_slice(FStar_Bytes_bytes b, uint32_t s, uint32_t e);

extern FStar_Bytes_bytes FStar_Bytes_slice_(FStar_Bytes_bytes b, Prims_int s, Prims_int e);

extern FStar_Bytes_bytes FStar_Bytes_sub(FStar_Bytes_bytes b, uint32_t s, uint32_t l);

typedef struct K___FStar_Bytes_bytes_FStar_Bytes_bytes_s
{
  FStar_Bytes_bytes fst;
  FStar_Bytes_bytes snd;
}
K___FStar_Bytes_bytes_FStar_Bytes_bytes;

extern K___FStar_Bytes_bytes_FStar_Bytes_bytes
FStar_Bytes_split(FStar_Bytes_bytes b, uint32_t k);

extern K___FStar_Bytes_bytes_FStar_Bytes_bytes
FStar_Bytes_split_(FStar_Bytes_bytes b, Prims_int k);

extern Prims_pos FStar_Bytes_repr_bytes(Prims_int n1);

extern Prims_int FStar_Bytes_int_of_bytes(FStar_Bytes_bytes b);

extern FStar_Bytes_bytes FStar_Bytes_bytes_of_int(Prims_int k, Prims_int n1);

extern uint32_t FStar_Bytes_int32_of_bytes(FStar_Bytes_bytes b);

extern uint16_t FStar_Bytes_int16_of_bytes(FStar_Bytes_bytes b);

extern uint8_t FStar_Bytes_int8_of_bytes(FStar_Bytes_bytes b);

extern FStar_Bytes_bytes FStar_Bytes_bytes_of_int32(uint32_t n1);

extern FStar_Bytes_bytes FStar_Bytes_bytes_of_int16(uint16_t n1);

extern FStar_Bytes_bytes FStar_Bytes_bytes_of_int8(uint8_t n1);

extern FStar_Bytes_bytes
FStar_Bytes_xor(uint32_t n1, FStar_Bytes_bytes b1, FStar_Bytes_bytes b2);

extern FStar_Bytes_bytes
FStar_Bytes_xor_(Prims_int n1, FStar_Bytes_bytes b1, FStar_Bytes_bytes b2);

extern FStar_Bytes_bytes FStar_Bytes_utf8_encode(Prims_string s);

#define FStar_Pervasives_Native_None 0
#define FStar_Pervasives_Native_Some 1

typedef uint8_t FStar_Pervasives_Native_option__Prims_string_tags;

typedef struct FStar_Pervasives_Native_option__Prims_string_s
{
  FStar_Pervasives_Native_option__Prims_string_tags tag;
  Prims_string v;
}
FStar_Pervasives_Native_option__Prims_string;

extern FStar_Pervasives_Native_option__Prims_string FStar_Bytes_iutf8_opt(FStar_Bytes_bytes m);

extern Prims_string FStar_Bytes_string_of_hex(Prims_string uu____763);

extern FStar_Bytes_bytes FStar_Bytes_bytes_of_hex(Prims_string uu____777);

extern Prims_string FStar_Bytes_hex_of_string(Prims_string uu____791);

extern Prims_string FStar_Bytes_hex_of_bytes(FStar_Bytes_bytes uu____805);

extern Prims_string FStar_Bytes_print_bytes(FStar_Bytes_bytes uu____819);

extern FStar_Bytes_bytes FStar_Bytes_bytes_of_string(Prims_string uu____833);

extern FStar_Bytes_bytes FStar_Bytes_of_buffer(uint32_t l, uint8_t *p);

extern void FStar_Bytes_store_bytes(FStar_Bytes_bytes src, uint8_t *dst);

#define __FStar_Bytes_H_DEFINED
#endif
