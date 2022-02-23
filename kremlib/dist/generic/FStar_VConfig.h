/*
  Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
  Licensed under the Apache 2.0 License.
*/


#ifndef __FStar_VConfig_H
#define __FStar_VConfig_H



#include "FStar_String.h"
#include "FStar_Bytes.h"
#include <inttypes.h>
#include "kremlib.h"
#include "kremlin/internal/compat.h"
#include "kremlin/internal/target.h"
typedef struct FStar_VConfig_vconfig_s
{
  Prims_int initial_fuel;
  Prims_int max_fuel;
  Prims_int initial_ifuel;
  Prims_int max_ifuel;
  bool detail_errors;
  bool detail_hint_replay;
  bool no_smt;
  Prims_int quake_lo;
  Prims_int quake_hi;
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
  FStar_Pervasives_Native_option__Prims_string vcgen_optimize_bind_as_seq;
  Prims_list__Prims_string *z3cliopt;
  bool z3refresh;
  Prims_int z3rlimit;
  Prims_int z3rlimit_factor;
  Prims_int z3seed;
  bool trivial_pre_for_unannotated_effectful_fns;
  FStar_Pervasives_Native_option__Prims_string reuse_hint_for;
}
FStar_VConfig_vconfig;


#define __FStar_VConfig_H_DEFINED
#endif
