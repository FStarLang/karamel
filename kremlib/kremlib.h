#ifndef __KREMLIB_H
#define __KREMLIB_H

#include <inttypes.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <stdbool.h>
#include <time.h>

// For types and values from C.fsti that do not exactly have the same name as
// their C counterparts
extern int exit_success;
extern int exit_failure;

typedef uint64_t FStar_UInt64_t, FStar_UInt64_t_;
typedef int64_t FStar_Int64_t, FStar_Int64_t_;
typedef uint32_t FStar_UInt32_t, FStar_UInt32_t_;
typedef int32_t FStar_Int32_t, FStar_Int32_t_;
typedef uint16_t FStar_UInt16_t, FStar_UInt16_t_;
typedef int16_t FStar_Int16_t, FStar_Int16_t_;
typedef uint8_t FStar_UInt8_t, FStar_UInt8_t_;
typedef int8_t FStar_Int8_t, FStar_Int8_t_;

#if defined(__GNUC__) && defined(__SIZEOF_INT128__)
typedef __int128 FStar_UInt128_t, FStar_UInt128_t_;
#define FStar_UInt128_add(x,y) ((x) + (y))
#define FStar_UInt128_mul(x,y) ((x) * (y))
#define FStar_UInt128_add_mod(x,y) ((x) + (y))
#define FStar_UInt128_sub(x,y) ((x) - (y))
#define FStar_UInt128_sub_mod(x,y) ((x) - (y))
#define FStar_UInt128_logand(x,y) ((x) & (y))
#define FStar_UInt128_logor(x,y) ((x) | (y))
#define FStar_UInt128_logxor(x,y) ((x) ^ (y))
#define FStar_UInt128_lognot(x) (~(x))
#define FStar_UInt128_shift_left(x, y) ((x) << (y))
#define FStar_UInt128_shift_right(x, y) ((x) >> (y))
#define FStar_Int_Cast_uint64_to_uint128(x) ((__int128)(x))
#define FStar_Int_Cast_uint128_to_uint64(x) ((uint64_t)(x))
#define FStar_UInt128_mul_wide(x, y) ((__int128)(x) * (y))
#else
typedef struct {
  uint64_t high;
  uint64_t low;
} FStar_UInt128_t, FStar_UInt128_t_;
FStar_UInt128_t FStar_UInt128_add(FStar_UInt128_t x, FStar_UInt128_t y);
FStar_UInt128_t FStar_UInt128_add_mod(FStar_UInt128_t x, FStar_UInt128_t y);
FStar_UInt128_t FStar_UInt128_sub(FStar_UInt128_t x, FStar_UInt128_t y);
FStar_UInt128_t FStar_UInt128_sub_mod(FStar_UInt128_t x, FStar_UInt128_t y);
FStar_UInt128_t FStar_UInt128_mul(FStar_UInt128_t x, FStar_UInt128_t y);
FStar_UInt128_t FStar_UInt128_logand(FStar_UInt128_t x, FStar_UInt128_t y);
FStar_UInt128_t FStar_UInt128_logor(FStar_UInt128_t x, FStar_UInt128_t y);
FStar_UInt128_t FStar_UInt128_logxor(FStar_UInt128_t x, FStar_UInt128_t y);
FStar_UInt128_t FStar_UInt128_lognot(FStar_UInt128_t x);
FStar_UInt128_t FStar_UInt128_shift_left(FStar_UInt128_t x, FStar_UInt32_t y);
FStar_UInt128_t FStar_UInt128_shift_right(FStar_UInt128_t x, FStar_UInt32_t y);
FStar_UInt128_t FStar_Int_Cast_uint64_to_uint128(uint64_t x);
uint64_t FStar_Int_Cast_uint128_to_uint64(FStar_UInt128_t x);
FStar_UInt128_t FStar_UInt128_mul_wide(uint64_t x, uint64_t y);
#endif

// Constant-time comparisons
uint64_t FStar_UInt64_eq_mask(uint64_t x, uint64_t y);
uint64_t FStar_UInt64_gte_mask(uint64_t x, uint64_t y);
uint32_t FStar_UInt32_eq_mask(uint32_t x, uint32_t y);
uint32_t FStar_UInt32_gte_mask(uint32_t x, uint32_t y);
uint8_t FStar_UInt8_eq_mask(uint8_t x, uint8_t y);
uint8_t FStar_UInt8_gte_mask(uint8_t x, uint8_t y);

// 128-bit arithmetic
FStar_UInt128_t FStar_UInt128_eq_mask(FStar_UInt128_t x, FStar_UInt128_t y);
FStar_UInt128_t FStar_UInt128_gte_mask(FStar_UInt128_t x, FStar_UInt128_t y);

// Some types that KreMLin has no special knowledge of; many of them appear in
// signatures of ghost functions, meaning that it suffices to give them (any)
// definition.
typedef void *Prims_pos, *Prims_nat, *Prims_nonzero, *FStar_Seq_seq, *Prims_int,
        *Prims_prop,
        *FStar_HyperStack_mem, *FStar_Set_set, *Prims_st_pre_h, *FStar_Heap_heap,
        *Prims_all_pre_h, *FStar_TSet_set, *Prims_string, *Prims_list,
        *FStar_Map_t,
        *FStar_UInt63_t_, *FStar_Int63_t_,
        *FStar_UInt63_t, *FStar_Int63_t,
        *FStar_UInt_uint_t, *FStar_Int_int_t,
        *FStar_HyperStack_stackref, *FStar_Bytes_bytes;

// Prims; all of the functions below abort;
bool Prims_op_GreaterThanOrEqual(Prims_int x, Prims_int y);
bool Prims_op_LessThanOrEqual(Prims_int x, Prims_int y);
bool Prims_op_GreaterThan(Prims_int x, Prims_int y);
bool Prims_op_LessThan(Prims_int x, Prims_int y);
Prims_int Prims_pow2(Prims_int x);
Prims_int Prims_op_Multiply(Prims_int x, Prims_int y);
Prims_int Prims_op_Addition(Prims_int x, Prims_int y);
Prims_int Prims_op_Subtraction(Prims_int x, Prims_int y);
Prims_int Prims_op_Division(Prims_int x, Prims_int y);
Prims_int Prims_op_Modulus(Prims_int x, Prims_int y);
void *Prims_magic(void *_);
void *Prims____Cons___tl(void *_);

// Stubs to make ST happy
bool FStar_HyperStack_is_eternal_color(Prims_int x0);
#define FStar_ST_op_Colon_Equals(x, v) exit(252)
#define FStar_ST_op_Bang(x) ((void*) 0)

// Misc; many of these are polymorphic, hence not extracted (yet) by Kremlin,
// which means that a macro is the "right" way to make they don't generate a
// compilation error.
Prims_int FStar_UInt32_v(uint32_t x);
#define FStar_Seq_createEmpty(x) ((void*)0)
#define FStar_Seq_create(len, init) ((void*)0)
#define FStar_Seq_upd(s, i, e) ((void*)0)
FStar_Seq_seq FStar_Seq_append(FStar_Seq_seq x, FStar_Seq_seq y);
FStar_Seq_seq FStar_SeqProperties_snoc(FStar_Seq_seq x, Prims_nat y);
FStar_Seq_seq FStar_SeqProperties_cons(int x, FStar_Seq_seq y);
int FStar_Seq_index(FStar_Seq_seq x, Prims_int y);

#endif
