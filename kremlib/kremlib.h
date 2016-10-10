#ifndef __KREMLIB_H
#define __KREMLIB_H

#include <inttypes.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <stdbool.h>

// For types and values from C.fsti that do not exactly have the same name as
// their C counterparts
extern int exit_success;
extern int exit_failure;

#ifdef __GNUC__
typedef __int128 FStar_UInt128_t, FStar_UInt128_t_;
#else
typedef void *FStar_UInt128_t, *FStar_UInt128_t_;
#endif
typedef uint64_t FStar_UInt64_t, FStar_UInt64_t_;
typedef int64_t FStar_Int64_t, FStar_Int64_t_;
typedef uint32_t FStar_UInt32_t, FStar_UInt32_t_;
typedef int32_t FStar_Int32_t, FStar_Int32_t_;
typedef uint16_t FStar_UInt16_t, FStar_UInt16_t_;
typedef int16_t FStar_Int16_t, FStar_Int16_t_;
typedef uint8_t FStar_UInt8_t, FStar_UInt8_t_;
typedef int8_t FStar_Int8_t, FStar_Int8_t_;

// These actually need to be properly implemented in C
uint64_t FStar_UInt64_eq_mask(uint64_t x, uint64_t y);
uint64_t FStar_UInt64_gte_mask(uint64_t x, uint64_t y);
uint8_t FStar_UInt8_eq_mask(uint8_t x, uint8_t y);
bool FStar_UInt128_op_Greater_Greater_Hat(FStar_UInt128_t x, FStar_UInt32_t y);

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
        *FStar_HyperStack_stackref,
        *FStar_Heap_aref, *FStar_Buffer_abuffer;

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

// Misc
Prims_int FStar_UInt32_v(uint32_t x);
FStar_Seq_seq FStar_Seq_createEmpty(void *_);
FStar_Seq_seq FStar_Seq_create(Prims_nat len, void *init);
FStar_Seq_seq FStar_Seq_append(FStar_Seq_seq x, FStar_Seq_seq y);
FStar_Seq_seq FStar_SeqProperties_snoc(FStar_Seq_seq x, Prims_nat y);
FStar_Seq_seq FStar_SeqProperties_cons(int x, FStar_Seq_seq y);
int FStar_Seq_index(FStar_Seq_seq x, Prims_int y);

#endif
