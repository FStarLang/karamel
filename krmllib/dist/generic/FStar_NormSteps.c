/*
  Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
  Licensed under the Apache 2.0 and MIT Licenses.
*/


#include "FStar_NormSteps.h"

#include "FStar_String.h"

bool FStar_NormSteps_uu___is_Simpl(FStar_NormSteps_norm_step projectee)
{
  if (projectee.tag == FStar_NormSteps_Simpl)
  {
    return true;
  }
  else
  {
    return false;
  }
}

bool FStar_NormSteps_uu___is_Weak(FStar_NormSteps_norm_step projectee)
{
  if (projectee.tag == FStar_NormSteps_Weak)
  {
    return true;
  }
  else
  {
    return false;
  }
}

bool FStar_NormSteps_uu___is_HNF(FStar_NormSteps_norm_step projectee)
{
  if (projectee.tag == FStar_NormSteps_HNF)
  {
    return true;
  }
  else
  {
    return false;
  }
}

bool FStar_NormSteps_uu___is_Primops(FStar_NormSteps_norm_step projectee)
{
  if (projectee.tag == FStar_NormSteps_Primops)
  {
    return true;
  }
  else
  {
    return false;
  }
}

bool FStar_NormSteps_uu___is_Delta(FStar_NormSteps_norm_step projectee)
{
  if (projectee.tag == FStar_NormSteps_Delta)
  {
    return true;
  }
  else
  {
    return false;
  }
}

bool FStar_NormSteps_uu___is_Zeta(FStar_NormSteps_norm_step projectee)
{
  if (projectee.tag == FStar_NormSteps_Zeta)
  {
    return true;
  }
  else
  {
    return false;
  }
}

bool FStar_NormSteps_uu___is_ZetaFull(FStar_NormSteps_norm_step projectee)
{
  if (projectee.tag == FStar_NormSteps_ZetaFull)
  {
    return true;
  }
  else
  {
    return false;
  }
}

bool FStar_NormSteps_uu___is_Iota(FStar_NormSteps_norm_step projectee)
{
  if (projectee.tag == FStar_NormSteps_Iota)
  {
    return true;
  }
  else
  {
    return false;
  }
}

bool FStar_NormSteps_uu___is_NBE(FStar_NormSteps_norm_step projectee)
{
  if (projectee.tag == FStar_NormSteps_NBE)
  {
    return true;
  }
  else
  {
    return false;
  }
}

bool FStar_NormSteps_uu___is_Reify(FStar_NormSteps_norm_step projectee)
{
  if (projectee.tag == FStar_NormSteps_Reify)
  {
    return true;
  }
  else
  {
    return false;
  }
}

bool FStar_NormSteps_uu___is_NormDebug(FStar_NormSteps_norm_step projectee)
{
  if (projectee.tag == FStar_NormSteps_NormDebug)
  {
    return true;
  }
  else
  {
    return false;
  }
}

bool FStar_NormSteps_uu___is_UnfoldOnly(FStar_NormSteps_norm_step projectee)
{
  if (projectee.tag == FStar_NormSteps_UnfoldOnly)
  {
    return true;
  }
  else
  {
    return false;
  }
}

bool FStar_NormSteps_uu___is_UnfoldOnce(FStar_NormSteps_norm_step projectee)
{
  if (projectee.tag == FStar_NormSteps_UnfoldOnce)
  {
    return true;
  }
  else
  {
    return false;
  }
}

bool FStar_NormSteps_uu___is_UnfoldFully(FStar_NormSteps_norm_step projectee)
{
  if (projectee.tag == FStar_NormSteps_UnfoldFully)
  {
    return true;
  }
  else
  {
    return false;
  }
}

bool FStar_NormSteps_uu___is_UnfoldAttr(FStar_NormSteps_norm_step projectee)
{
  if (projectee.tag == FStar_NormSteps_UnfoldAttr)
  {
    return true;
  }
  else
  {
    return false;
  }
}

bool FStar_NormSteps_uu___is_UnfoldQual(FStar_NormSteps_norm_step projectee)
{
  if (projectee.tag == FStar_NormSteps_UnfoldQual)
  {
    return true;
  }
  else
  {
    return false;
  }
}

bool FStar_NormSteps_uu___is_UnfoldNamespace(FStar_NormSteps_norm_step projectee)
{
  if (projectee.tag == FStar_NormSteps_UnfoldNamespace)
  {
    return true;
  }
  else
  {
    return false;
  }
}

bool FStar_NormSteps_uu___is_Unmeta(FStar_NormSteps_norm_step projectee)
{
  if (projectee.tag == FStar_NormSteps_Unmeta)
  {
    return true;
  }
  else
  {
    return false;
  }
}

bool FStar_NormSteps_uu___is_Unascribe(FStar_NormSteps_norm_step projectee)
{
  if (projectee.tag == FStar_NormSteps_Unascribe)
  {
    return true;
  }
  else
  {
    return false;
  }
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

