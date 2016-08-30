#ifndef __KREMLIB_H
#define __KREMLIB_H

#include <inttypes.h>

// Types and values exposed via C.fsti
typedef char C_char;
typedef int C_int;
extern int C_exit_success;

// Some types that KreMLin has no special knowledge of; many of them appear in
// signatures of ghost functions, meaning that it suffices to give them (any)
// definition.
typedef __int128 FStar_UInt128_t, FStar_UInt128_t_;
typedef uint64_t FStar_UInt64_t, FStar_UInt64_t_;
typedef int64_t FStar_Int64_t, FStar_Int64_t_;
typedef uint32_t FStar_UInt32_t, FStar_UInt32_t_;
typedef int32_t FStar_Int32_t, FStar_Int32_t_;
typedef uint16_t FStar_UInt16_t, FStar_UInt16_t_;
typedef int16_t FStar_Int16_t, FStar_Int16_t_;
typedef uint8_t FStar_UInt8_t, FStar_UInt8_t_;
typedef int8_t FStar_Int8_t, FStar_Int8_t_;

typedef void *Prims_pos, *Prims_nat, *FStar_Seq_seq, *Prims_int,
        *FStar_HyperStack_mem, *FStar_Set_set, *Prims_st_pre_h,
        *Prims_all_pre_h, *FStar_TSet_set, *Prims_string, *Prims_list,
        *FStar_Map_t,
        *FStar_UInt63_t_, *FStar_Int63_t_,
        *FStar_UInt_uint_t, *FStar_Int_int_t;

// Some actual functions that are expected to be realized in C.
uint64_t FStar_UInt64_gte_mask(uint64_t x, uint64_t y);
uint64_t FStar_UInt64_eq_mask(uint64_t x, uint64_t y);

#endif
