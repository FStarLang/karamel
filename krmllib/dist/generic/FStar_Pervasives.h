/*
  Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
  Licensed under the Apache 2.0 and MIT Licenses.
*/


#ifndef __FStar_Pervasives_H
#define __FStar_Pervasives_H

#include <inttypes.h>
#include "krmllib.h"
#include "krml/internal/compat.h"
#include "krml/internal/target.h"

typedef void *FStar_Pervasives_pattern;

typedef void *FStar_Pervasives_eqtype_u;

typedef void *FStar_Pervasives_trivial_pure_post;

typedef void *FStar_Pervasives_ambient;

typedef void *FStar_Pervasives_pure_return;

typedef void *FStar_Pervasives_pure_if_then_else;

typedef void *FStar_Pervasives_pure_ite_wp;

typedef void *FStar_Pervasives_pure_close_wp;

typedef void *FStar_Pervasives_pure_null_wp;

typedef void *FStar_Pervasives_pure_assert_wp;

typedef void *FStar_Pervasives_pure_assume_wp;

typedef void *FStar_Pervasives_div_hoare_to_wp;

typedef void *FStar_Pervasives_st_pre_h;

typedef void *FStar_Pervasives_st_post_h_;

typedef void *FStar_Pervasives_st_post_h;

typedef void *FStar_Pervasives_st_wp_h;

typedef void *FStar_Pervasives_st_if_then_else;

typedef void *FStar_Pervasives_st_ite_wp;

typedef void *FStar_Pervasives_st_stronger;

typedef void *FStar_Pervasives_st_close_wp;

typedef void *FStar_Pervasives_st_trivial;

typedef void *FStar_Pervasives_ex_pre;

typedef void *FStar_Pervasives_ex_post_;

typedef void *FStar_Pervasives_ex_post;

typedef void *FStar_Pervasives_ex_wp;

typedef void *FStar_Pervasives_ex_bind_wp;

typedef void *FStar_Pervasives_ex_if_then_else;

typedef void *FStar_Pervasives_ex_ite_wp;

typedef void *FStar_Pervasives_ex_stronger;

typedef void *FStar_Pervasives_ex_close_wp;

typedef void *FStar_Pervasives_all_pre_h;

typedef void *FStar_Pervasives_all_post_h_;

typedef void *FStar_Pervasives_all_post_h;

typedef void *FStar_Pervasives_all_wp_h;

typedef void *FStar_Pervasives_all_if_then_else;

typedef void *FStar_Pervasives_all_ite_wp;

typedef void *FStar_Pervasives_all_stronger;

typedef void *FStar_Pervasives_all_close_wp;

typedef void *FStar_Pervasives_all_trivial;

typedef void *FStar_Pervasives_inversion;


#define __FStar_Pervasives_H_DEFINED
#endif
