/*
  Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
  Licensed under the Apache 2.0 and MIT Licenses.
*/


#ifndef KRML_HEADER_FStar_ST_H
#define KRML_HEADER_FStar_ST_H

#include "FStar_Monotonic_Heap.h"
#include <inttypes.h>
#include "krmllib.h"
#include "krml/internal/compat.h"
#include "krml/internal/target.h"

typedef void *FStar_ST_gst_pre;

typedef void *FStar_ST_gst_post_;

typedef void *FStar_ST_gst_post;

typedef void *FStar_ST_gst_wp;

typedef void *FStar_ST_heap_rel;

extern FStar_Monotonic_Heap_heap_rec FStar_ST_gst_get(void);

extern void FStar_ST_gst_put(FStar_Monotonic_Heap_heap_rec h1);

typedef void *FStar_ST_heap_predicate;

typedef void *FStar_ST_stable;

typedef void *FStar_ST_st_pre;

typedef void *FStar_ST_st_post_;

typedef void *FStar_ST_st_post;

typedef void *FStar_ST_st_wp;

typedef void *FStar_ST_contains_pred;

extern FStar_Monotonic_Heap_heap_rec FStar_ST_get(void);

typedef void *FStar_ST_modifies_none;


#define KRML_HEADER_FStar_ST_H_DEFINED
#endif /* KRML_HEADER_FStar_ST_H */
