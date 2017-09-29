#ifndef __KREMBYTES_H
#define __KREMBYTES_H

#include "kremlib.h"
#include "FStar.h"

typedef struct
{
    uint8_t fst;
    uint8_t snd;
} K___uint8_t_uint8_t;

typedef struct
{
    FStar_Bytes_bytes fst;
    FStar_Bytes_bytes snd;
} K___FStar_Bytes_bytes_FStar_Bytes_bytes;

/* Bytes */
extern FStar_Bytes_bytes FStar_Bytes_create(FStar_UInt32_t x, uint8_t y);
extern krml_checked_int_t FStar_Bytes_len(FStar_Bytes_bytes bs);
extern K___FStar_Bytes_bytes_FStar_Bytes_bytes FStar_Bytes_split(FStar_Bytes_bytes bs, FStar_UInt32_t i);
extern FStar_Bytes_bytes FStar_Bytes_append(FStar_Bytes_bytes b1, FStar_Bytes_bytes b2);
extern FStar_Bytes_bytes FStar_Bytes_xor(FStar_UInt32_t x, FStar_Bytes_bytes b1, FStar_Bytes_bytes b2);
extern FStar_Bytes_bytes FStar_Bytes_bytes_of_int(krml_checked_int_t k, krml_checked_int_t n);
extern krml_checked_int_t FStar_Bytes_int_of_bytes(FStar_Bytes_bytes bs);
extern FStar_Bytes_bytes FStar_Bytes_twobytes(K___uint8_t_uint8_t two_bytes);
extern int FStar_Bytes_get(FStar_Bytes_bytes bs, uint32_t i);
extern int FStar_Bytes_repr_bytes(Prims_nat bs);
extern FStar_Bytes_bytes FStar_Bytes_abyte(uint8_t byte);
extern FStar_Bytes_bytes FStar_Bytes_utf8_encode(Prims_string str);
extern FStar_Bytes_bytes FStar_Bytes_bytes_of_hex(Prims_string str);
static FStar_Bytes_bytes FStar_Bytes_empty_bytes;

#endif
