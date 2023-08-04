/*
  Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
  Licensed under the Apache 2.0 License.
*/


#ifndef __FStar_VConfig_H
#define __FStar_VConfig_H

#include "FStar_String.h"
#include "FStar_Bytes.h"
#include <inttypes.h>
#include "krmllib.h"
#include "krml/internal/compat.h"
#include "krml/internal/target.h"

typedef struct FStar_VConfig_vconfig_s
{
  krml_checked_int_t initial_fuel;
  krml_checked_int_t max_fuel;
  krml_checked_int_t initial_ifuel;
  krml_checked_int_t max_ifuel;
  bool detail_errors;
  bool detail_hint_replay;
  bool no_smt;
  krml_checked_int_t quake_lo;
  krml_checked_int_t quake_hi;
  bool quake_keep;
  bool retry;
  bool smtencoding_elim_box;
  Prims_string smtencoding_nl_arith_repr;
  Prims_string smtencoding_l_arith_repr;
  bool smtencoding_valid_intro;
  bool smtencoding_valid_elim;
  bool tcnorm;
  bool no_plugins;
  bool no_tactics;
  Prims_list__Prims_string *z3cliopt;
  Prims_list__Prims_string *z3smtopt;
  bool z3refresh;
  krml_checked_int_t z3rlimit;
  krml_checked_int_t z3rlimit_factor;
  krml_checked_int_t z3seed;
  bool trivial_pre_for_unannotated_effectful_fns;
  FStar_Pervasives_Native_option__Prims_string reuse_hint_for;
}
FStar_VConfig_vconfig;


#define __FStar_VConfig_H_DEFINED
#endif
