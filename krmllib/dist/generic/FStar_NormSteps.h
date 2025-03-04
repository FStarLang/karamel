/*
  Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
  Licensed under the Apache 2.0 and MIT Licenses.
*/


#ifndef __FStar_NormSteps_H
#define __FStar_NormSteps_H

#include "FStar_String.h"
#include <inttypes.h>
#include "krmllib.h"
#include "krml/internal/compat.h"
#include "krml/internal/target.h"

#define FStar_NormSteps_Simpl 0
#define FStar_NormSteps_Weak 1
#define FStar_NormSteps_HNF 2
#define FStar_NormSteps_Primops 3
#define FStar_NormSteps_Delta 4
#define FStar_NormSteps_Zeta 5
#define FStar_NormSteps_ZetaFull 6
#define FStar_NormSteps_Iota 7
#define FStar_NormSteps_NBE 8
#define FStar_NormSteps_Reify 9
#define FStar_NormSteps_NormDebug 10
#define FStar_NormSteps_UnfoldOnly 11
#define FStar_NormSteps_UnfoldOnce 12
#define FStar_NormSteps_UnfoldFully 13
#define FStar_NormSteps_UnfoldAttr 14
#define FStar_NormSteps_UnfoldQual 15
#define FStar_NormSteps_UnfoldNamespace 16
#define FStar_NormSteps_Unmeta 17
#define FStar_NormSteps_Unascribe 18

typedef uint8_t FStar_NormSteps_norm_step_tags;

typedef struct FStar_NormSteps_norm_step_s
{
  FStar_NormSteps_norm_step_tags tag;
  union {
    Prims_list__Prims_string *case_UnfoldOnly;
    Prims_list__Prims_string *case_UnfoldOnce;
    Prims_list__Prims_string *case_UnfoldFully;
    Prims_list__Prims_string *case_UnfoldAttr;
    Prims_list__Prims_string *case_UnfoldQual;
    Prims_list__Prims_string *case_UnfoldNamespace;
  }
  ;
}
FStar_NormSteps_norm_step;

bool FStar_NormSteps_uu___is_Simpl(FStar_NormSteps_norm_step projectee);

bool FStar_NormSteps_uu___is_Weak(FStar_NormSteps_norm_step projectee);

bool FStar_NormSteps_uu___is_HNF(FStar_NormSteps_norm_step projectee);

bool FStar_NormSteps_uu___is_Primops(FStar_NormSteps_norm_step projectee);

bool FStar_NormSteps_uu___is_Delta(FStar_NormSteps_norm_step projectee);

bool FStar_NormSteps_uu___is_Zeta(FStar_NormSteps_norm_step projectee);

bool FStar_NormSteps_uu___is_ZetaFull(FStar_NormSteps_norm_step projectee);

bool FStar_NormSteps_uu___is_Iota(FStar_NormSteps_norm_step projectee);

bool FStar_NormSteps_uu___is_NBE(FStar_NormSteps_norm_step projectee);

bool FStar_NormSteps_uu___is_Reify(FStar_NormSteps_norm_step projectee);

bool FStar_NormSteps_uu___is_NormDebug(FStar_NormSteps_norm_step projectee);

bool FStar_NormSteps_uu___is_UnfoldOnly(FStar_NormSteps_norm_step projectee);

bool FStar_NormSteps_uu___is_UnfoldOnce(FStar_NormSteps_norm_step projectee);

bool FStar_NormSteps_uu___is_UnfoldFully(FStar_NormSteps_norm_step projectee);

bool FStar_NormSteps_uu___is_UnfoldAttr(FStar_NormSteps_norm_step projectee);

bool FStar_NormSteps_uu___is_UnfoldQual(FStar_NormSteps_norm_step projectee);

bool FStar_NormSteps_uu___is_UnfoldNamespace(FStar_NormSteps_norm_step projectee);

bool FStar_NormSteps_uu___is_Unmeta(FStar_NormSteps_norm_step projectee);

bool FStar_NormSteps_uu___is_Unascribe(FStar_NormSteps_norm_step projectee);

extern FStar_NormSteps_norm_step FStar_NormSteps_simplify;

extern FStar_NormSteps_norm_step FStar_NormSteps_weak;

extern FStar_NormSteps_norm_step FStar_NormSteps_hnf;

extern FStar_NormSteps_norm_step FStar_NormSteps_primops;

extern FStar_NormSteps_norm_step FStar_NormSteps_delta;

extern FStar_NormSteps_norm_step FStar_NormSteps_norm_debug;

extern FStar_NormSteps_norm_step FStar_NormSteps_zeta;

extern FStar_NormSteps_norm_step FStar_NormSteps_zeta_full;

extern FStar_NormSteps_norm_step FStar_NormSteps_iota;

extern FStar_NormSteps_norm_step FStar_NormSteps_nbe;

extern FStar_NormSteps_norm_step FStar_NormSteps_reify_;

FStar_NormSteps_norm_step FStar_NormSteps_delta_only(Prims_list__Prims_string *s);

FStar_NormSteps_norm_step FStar_NormSteps_delta_once(Prims_list__Prims_string *s);

FStar_NormSteps_norm_step FStar_NormSteps_delta_fully(Prims_list__Prims_string *s);

FStar_NormSteps_norm_step FStar_NormSteps_delta_attr(Prims_list__Prims_string *s);

FStar_NormSteps_norm_step FStar_NormSteps_delta_qualifier(Prims_list__Prims_string *s);

FStar_NormSteps_norm_step FStar_NormSteps_delta_namespace(Prims_list__Prims_string *s);

extern FStar_NormSteps_norm_step FStar_NormSteps_unmeta;

extern FStar_NormSteps_norm_step FStar_NormSteps_unascribe;


#define __FStar_NormSteps_H_DEFINED
#endif
