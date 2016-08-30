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
typedef __int128 FStar_UInt128_t;
typedef void *Prims_pos, *Prims_nat, *FStar_Seq_seq, *Prims_int, *FStar_HyperStack_mem;

Prims_int FStar_UInt32_v(uint32_t x);

// Some actual functions that are expected to be realized in C.
uint64_t FStar_UInt64_gte_mask(uint64_t x, uint64_t y);
uint64_t FStar_UInt64_eq_mask(uint64_t x, uint64_t y);

#endif
