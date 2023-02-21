/*
  Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
  Licensed under the Apache 2.0 License.
*/


#ifndef __FStar_Monotonic_Heap_H
#define __FStar_Monotonic_Heap_H

#include "FStar_Bytes.h"
#include <inttypes.h>
#include "krmllib.h"
#include "krml/internal/compat.h"
#include "krml/internal/target.h"

typedef void *FStar_Monotonic_Heap_tset;

typedef struct FStar_Pervasives_dtuple4_____FStar_Pervasives_Native_option_____bool_any_s
{
  FStar_Pervasives_Native_option__Prims_string_tags _2;
  bool _3;
}
FStar_Pervasives_dtuple4_____FStar_Pervasives_Native_option_____bool_any;

typedef struct
FStar_Pervasives_Native_option__FStar_Pervasives_dtuple4____FStar_Pervasives_Native_option_____bool_any_s
{
  FStar_Pervasives_Native_option__Prims_string_tags tag;
  FStar_Pervasives_dtuple4_____FStar_Pervasives_Native_option_____bool_any v;
}
FStar_Pervasives_Native_option__FStar_Pervasives_dtuple4____FStar_Pervasives_Native_option_____bool_any;

typedef struct FStar_Monotonic_Heap_heap_rec_s
{
  Prims_pos next_addr;
  FStar_Pervasives_Native_option__FStar_Pervasives_dtuple4____FStar_Pervasives_Native_option_____bool_any
  (*memory)(Prims_pos x0);
}
FStar_Monotonic_Heap_heap_rec;

typedef FStar_Monotonic_Heap_heap_rec FStar_Monotonic_Heap_heap;

typedef void *FStar_Monotonic_Heap_equal;

extern FStar_Monotonic_Heap_heap_rec FStar_Monotonic_Heap_emp;

typedef void *FStar_Monotonic_Heap_contains;

typedef void *FStar_Monotonic_Heap_addr_unused_in;

typedef void *FStar_Monotonic_Heap_unused_in;

typedef void *FStar_Monotonic_Heap_fresh;

typedef void *FStar_Monotonic_Heap_modifies_t;

typedef void *FStar_Monotonic_Heap_modifies;

typedef void *FStar_Monotonic_Heap_equal_dom;

typedef struct FStar_Monotonic_Heap_aref__s
{
  Prims_int a_addr;
  bool a_mm;
}
FStar_Monotonic_Heap_aref_;

typedef FStar_Monotonic_Heap_aref_ FStar_Monotonic_Heap_aref;

extern FStar_Monotonic_Heap_aref_ FStar_Monotonic_Heap_dummy_aref;

typedef void *FStar_Monotonic_Heap_aref_unused_in;

typedef void *FStar_Monotonic_Heap_aref_live_at;

extern void
**FStar_Monotonic_Heap_ref_of(FStar_Monotonic_Heap_heap_rec h, FStar_Monotonic_Heap_aref_ a);


#define __FStar_Monotonic_Heap_H_DEFINED
#endif
