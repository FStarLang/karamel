/*
  Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
  Licensed under the Apache 2.0 License.
*/


#ifndef __FStar_VConfig_H
#define __FStar_VConfig_H
#include <inttypes.h>
#include "kremlib.h"
#include "kremlin/internal/compat.h"
#include "kremlin/internal/target.h"


#include "FStar_String.h"
#include "FStar_Bytes.h"

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
  bool use_two_phase_tc;
  bool trivial_pre_for_unannotated_effectful_fns;
  FStar_Pervasives_Native_option__Prims_string reuse_hint_for;
}
FStar_VConfig_vconfig;

Prims_int FStar_VConfig___proj__Mkvconfig__item__initial_fuel(FStar_VConfig_vconfig projectee);

Prims_int FStar_VConfig___proj__Mkvconfig__item__max_fuel(FStar_VConfig_vconfig projectee);

Prims_int
FStar_VConfig___proj__Mkvconfig__item__initial_ifuel(FStar_VConfig_vconfig projectee);

Prims_int FStar_VConfig___proj__Mkvconfig__item__max_ifuel(FStar_VConfig_vconfig projectee);

bool FStar_VConfig___proj__Mkvconfig__item__detail_errors(FStar_VConfig_vconfig projectee);

bool
FStar_VConfig___proj__Mkvconfig__item__detail_hint_replay(FStar_VConfig_vconfig projectee);

bool FStar_VConfig___proj__Mkvconfig__item__no_smt(FStar_VConfig_vconfig projectee);

Prims_int FStar_VConfig___proj__Mkvconfig__item__quake_lo(FStar_VConfig_vconfig projectee);

Prims_int FStar_VConfig___proj__Mkvconfig__item__quake_hi(FStar_VConfig_vconfig projectee);

bool FStar_VConfig___proj__Mkvconfig__item__quake_keep(FStar_VConfig_vconfig projectee);

bool FStar_VConfig___proj__Mkvconfig__item__retry(FStar_VConfig_vconfig projectee);

bool
FStar_VConfig___proj__Mkvconfig__item__smtencoding_elim_box(FStar_VConfig_vconfig projectee);

Prims_string
FStar_VConfig___proj__Mkvconfig__item__smtencoding_nl_arith_repr(
  FStar_VConfig_vconfig projectee
);

Prims_string
FStar_VConfig___proj__Mkvconfig__item__smtencoding_l_arith_repr(
  FStar_VConfig_vconfig projectee
);

bool
FStar_VConfig___proj__Mkvconfig__item__smtencoding_valid_intro(FStar_VConfig_vconfig projectee);

bool
FStar_VConfig___proj__Mkvconfig__item__smtencoding_valid_elim(FStar_VConfig_vconfig projectee);

bool FStar_VConfig___proj__Mkvconfig__item__tcnorm(FStar_VConfig_vconfig projectee);

bool FStar_VConfig___proj__Mkvconfig__item__no_plugins(FStar_VConfig_vconfig projectee);

bool FStar_VConfig___proj__Mkvconfig__item__no_tactics(FStar_VConfig_vconfig projectee);

FStar_Pervasives_Native_option__Prims_string
FStar_VConfig___proj__Mkvconfig__item__vcgen_optimize_bind_as_seq(
  FStar_VConfig_vconfig projectee
);

Prims_list__Prims_string
*FStar_VConfig___proj__Mkvconfig__item__z3cliopt(FStar_VConfig_vconfig projectee);

bool FStar_VConfig___proj__Mkvconfig__item__z3refresh(FStar_VConfig_vconfig projectee);

Prims_int FStar_VConfig___proj__Mkvconfig__item__z3rlimit(FStar_VConfig_vconfig projectee);

Prims_int
FStar_VConfig___proj__Mkvconfig__item__z3rlimit_factor(FStar_VConfig_vconfig projectee);

Prims_int FStar_VConfig___proj__Mkvconfig__item__z3seed(FStar_VConfig_vconfig projectee);

bool FStar_VConfig___proj__Mkvconfig__item__use_two_phase_tc(FStar_VConfig_vconfig projectee);

bool
FStar_VConfig___proj__Mkvconfig__item__trivial_pre_for_unannotated_effectful_fns(
  FStar_VConfig_vconfig projectee
);

FStar_Pervasives_Native_option__Prims_string
FStar_VConfig___proj__Mkvconfig__item__reuse_hint_for(FStar_VConfig_vconfig projectee);


#define __FStar_VConfig_H_DEFINED
#endif
