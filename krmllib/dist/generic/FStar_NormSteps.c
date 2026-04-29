/*
  Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
  Licensed under the Apache 2.0 and MIT Licenses.
*/


#include "FStar_NormSteps.h"

#include "FStar_String.h"

bool FStar_NormSteps_uu___is_Simpl(FStar_NormSteps_norm_step projectee)
{
  return projectee.tag == FStar_NormSteps_Simpl;
}

bool FStar_NormSteps_uu___is_Weak(FStar_NormSteps_norm_step projectee)
{
  return projectee.tag == FStar_NormSteps_Weak;
}

bool FStar_NormSteps_uu___is_HNF(FStar_NormSteps_norm_step projectee)
{
  return projectee.tag == FStar_NormSteps_HNF;
}

bool FStar_NormSteps_uu___is_Primops(FStar_NormSteps_norm_step projectee)
{
  return projectee.tag == FStar_NormSteps_Primops;
}

bool FStar_NormSteps_uu___is_Delta(FStar_NormSteps_norm_step projectee)
{
  return projectee.tag == FStar_NormSteps_Delta;
}

bool FStar_NormSteps_uu___is_Zeta(FStar_NormSteps_norm_step projectee)
{
  return projectee.tag == FStar_NormSteps_Zeta;
}

bool FStar_NormSteps_uu___is_ZetaFull(FStar_NormSteps_norm_step projectee)
{
  return projectee.tag == FStar_NormSteps_ZetaFull;
}

bool FStar_NormSteps_uu___is_Iota(FStar_NormSteps_norm_step projectee)
{
  return projectee.tag == FStar_NormSteps_Iota;
}

bool FStar_NormSteps_uu___is_NBE(FStar_NormSteps_norm_step projectee)
{
  return projectee.tag == FStar_NormSteps_NBE;
}

bool FStar_NormSteps_uu___is_Reify(FStar_NormSteps_norm_step projectee)
{
  return projectee.tag == FStar_NormSteps_Reify;
}

bool FStar_NormSteps_uu___is_NormDebug(FStar_NormSteps_norm_step projectee)
{
  return projectee.tag == FStar_NormSteps_NormDebug;
}

bool FStar_NormSteps_uu___is_UnfoldOnly(FStar_NormSteps_norm_step projectee)
{
  return projectee.tag == FStar_NormSteps_UnfoldOnly;
}

bool FStar_NormSteps_uu___is_UnfoldOnce(FStar_NormSteps_norm_step projectee)
{
  return projectee.tag == FStar_NormSteps_UnfoldOnce;
}

bool FStar_NormSteps_uu___is_UnfoldFully(FStar_NormSteps_norm_step projectee)
{
  return projectee.tag == FStar_NormSteps_UnfoldFully;
}

bool FStar_NormSteps_uu___is_UnfoldAttr(FStar_NormSteps_norm_step projectee)
{
  return projectee.tag == FStar_NormSteps_UnfoldAttr;
}

bool FStar_NormSteps_uu___is_UnfoldQual(FStar_NormSteps_norm_step projectee)
{
  return projectee.tag == FStar_NormSteps_UnfoldQual;
}

bool FStar_NormSteps_uu___is_UnfoldNamespace(FStar_NormSteps_norm_step projectee)
{
  return projectee.tag == FStar_NormSteps_UnfoldNamespace;
}

bool FStar_NormSteps_uu___is_Unmeta(FStar_NormSteps_norm_step projectee)
{
  return projectee.tag == FStar_NormSteps_Unmeta;
}

bool FStar_NormSteps_uu___is_Unascribe(FStar_NormSteps_norm_step projectee)
{
  return projectee.tag == FStar_NormSteps_Unascribe;
}

FStar_NormSteps_norm_step FStar_NormSteps_simplify = { .tag = FStar_NormSteps_Simpl };

FStar_NormSteps_norm_step FStar_NormSteps_weak = { .tag = FStar_NormSteps_Weak };

FStar_NormSteps_norm_step FStar_NormSteps_hnf = { .tag = FStar_NormSteps_HNF };

FStar_NormSteps_norm_step FStar_NormSteps_primops = { .tag = FStar_NormSteps_Primops };

FStar_NormSteps_norm_step FStar_NormSteps_delta = { .tag = FStar_NormSteps_Delta };

FStar_NormSteps_norm_step FStar_NormSteps_norm_debug = { .tag = FStar_NormSteps_NormDebug };

FStar_NormSteps_norm_step FStar_NormSteps_zeta = { .tag = FStar_NormSteps_Zeta };

FStar_NormSteps_norm_step FStar_NormSteps_zeta_full = { .tag = FStar_NormSteps_ZetaFull };

FStar_NormSteps_norm_step FStar_NormSteps_iota = { .tag = FStar_NormSteps_Iota };

FStar_NormSteps_norm_step FStar_NormSteps_nbe = { .tag = FStar_NormSteps_NBE };

FStar_NormSteps_norm_step FStar_NormSteps_reify_ = { .tag = FStar_NormSteps_Reify };

FStar_NormSteps_norm_step FStar_NormSteps_delta_only(Prims_list__Prims_string *s)
{
  return
    ((FStar_NormSteps_norm_step){ .tag = FStar_NormSteps_UnfoldOnly, { .case_UnfoldOnly = s } });
}

FStar_NormSteps_norm_step FStar_NormSteps_delta_once(Prims_list__Prims_string *s)
{
  return
    ((FStar_NormSteps_norm_step){ .tag = FStar_NormSteps_UnfoldOnce, { .case_UnfoldOnce = s } });
}

FStar_NormSteps_norm_step FStar_NormSteps_delta_fully(Prims_list__Prims_string *s)
{
  return
    ((FStar_NormSteps_norm_step){ .tag = FStar_NormSteps_UnfoldFully, { .case_UnfoldFully = s } });
}

FStar_NormSteps_norm_step FStar_NormSteps_delta_attr(Prims_list__Prims_string *s)
{
  return
    ((FStar_NormSteps_norm_step){ .tag = FStar_NormSteps_UnfoldAttr, { .case_UnfoldAttr = s } });
}

FStar_NormSteps_norm_step FStar_NormSteps_delta_qualifier(Prims_list__Prims_string *s)
{
  return
    ((FStar_NormSteps_norm_step){ .tag = FStar_NormSteps_UnfoldQual, { .case_UnfoldQual = s } });
}

FStar_NormSteps_norm_step FStar_NormSteps_delta_namespace(Prims_list__Prims_string *s)
{
  return
    (
      (FStar_NormSteps_norm_step){
        .tag = FStar_NormSteps_UnfoldNamespace,
        { .case_UnfoldNamespace = s }
      }
    );
}

FStar_NormSteps_norm_step FStar_NormSteps_unmeta = { .tag = FStar_NormSteps_Unmeta };

FStar_NormSteps_norm_step FStar_NormSteps_unascribe = { .tag = FStar_NormSteps_Unascribe };

