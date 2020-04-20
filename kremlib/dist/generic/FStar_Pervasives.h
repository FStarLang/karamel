/*
  Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
  Licensed under the Apache 2.0 License.
*/

#include <inttypes.h>
#include "kremlib.h"
#include "kremlin/internal/compat.h"
#include "kremlin/internal/target.h"

#ifndef __FStar_Pervasives_H
#define __FStar_Pervasives_H

#include "FStar_String.h"
#include "FStar_BitVector.h"


typedef void *FStar_Pervasives_ex_pre;

#define FStar_Pervasives_PpxDerivingShow 0
#define FStar_Pervasives_PpxDerivingShowConstant 1
#define FStar_Pervasives_PpxDerivingYoJson 2
#define FStar_Pervasives_CInline 3
#define FStar_Pervasives_Substitute 4
#define FStar_Pervasives_Gc 5
#define FStar_Pervasives_Comment 6
#define FStar_Pervasives_CPrologue 7
#define FStar_Pervasives_CEpilogue 8
#define FStar_Pervasives_CConst 9
#define FStar_Pervasives_CCConv 10
#define FStar_Pervasives_CAbstractStruct 11
#define FStar_Pervasives_CIfDef 12
#define FStar_Pervasives_CMacro 13

typedef uint8_t FStar_Pervasives___internal_ocaml_attributes_tags;

typedef struct FStar_Pervasives___internal_ocaml_attributes_s
{
  FStar_Pervasives___internal_ocaml_attributes_tags tag;
  union {
    Prims_string case_PpxDerivingShowConstant;
    Prims_string case_Comment;
    Prims_string case_CPrologue;
    Prims_string case_CEpilogue;
    Prims_string case_CConst;
    Prims_string case_CCConv;
  }
  ;
}
FStar_Pervasives___internal_ocaml_attributes;

extern bool
FStar_Pervasives_uu___is_PpxDerivingShow(
  FStar_Pervasives___internal_ocaml_attributes projectee
);

extern bool
FStar_Pervasives_uu___is_PpxDerivingShowConstant(
  FStar_Pervasives___internal_ocaml_attributes projectee
);

extern Prims_string
FStar_Pervasives___proj__PpxDerivingShowConstant__item___0(
  FStar_Pervasives___internal_ocaml_attributes projectee
);

extern bool
FStar_Pervasives_uu___is_PpxDerivingYoJson(
  FStar_Pervasives___internal_ocaml_attributes projectee
);

extern bool
FStar_Pervasives_uu___is_CInline(FStar_Pervasives___internal_ocaml_attributes projectee);

extern bool
FStar_Pervasives_uu___is_Substitute(FStar_Pervasives___internal_ocaml_attributes projectee);

extern bool
FStar_Pervasives_uu___is_Gc(FStar_Pervasives___internal_ocaml_attributes projectee);

extern bool
FStar_Pervasives_uu___is_Comment(FStar_Pervasives___internal_ocaml_attributes projectee);

extern Prims_string
FStar_Pervasives___proj__Comment__item___0(
  FStar_Pervasives___internal_ocaml_attributes projectee
);

extern bool
FStar_Pervasives_uu___is_CPrologue(FStar_Pervasives___internal_ocaml_attributes projectee);

extern Prims_string
FStar_Pervasives___proj__CPrologue__item___0(
  FStar_Pervasives___internal_ocaml_attributes projectee
);

extern bool
FStar_Pervasives_uu___is_CEpilogue(FStar_Pervasives___internal_ocaml_attributes projectee);

extern Prims_string
FStar_Pervasives___proj__CEpilogue__item___0(
  FStar_Pervasives___internal_ocaml_attributes projectee
);

extern bool
FStar_Pervasives_uu___is_CConst(FStar_Pervasives___internal_ocaml_attributes projectee);

extern Prims_string
FStar_Pervasives___proj__CConst__item___0(
  FStar_Pervasives___internal_ocaml_attributes projectee
);

extern bool
FStar_Pervasives_uu___is_CCConv(FStar_Pervasives___internal_ocaml_attributes projectee);

extern Prims_string
FStar_Pervasives___proj__CCConv__item___0(
  FStar_Pervasives___internal_ocaml_attributes projectee
);

extern bool
FStar_Pervasives_uu___is_CAbstractStruct(
  FStar_Pervasives___internal_ocaml_attributes projectee
);

extern bool
FStar_Pervasives_uu___is_CIfDef(FStar_Pervasives___internal_ocaml_attributes projectee);

extern bool
FStar_Pervasives_uu___is_CMacro(FStar_Pervasives___internal_ocaml_attributes projectee);

#define FStar_Pervasives_Simpl 0
#define FStar_Pervasives_Weak 1
#define FStar_Pervasives_HNF 2
#define FStar_Pervasives_Primops 3
#define FStar_Pervasives_Delta 4
#define FStar_Pervasives_Zeta 5
#define FStar_Pervasives_ZetaFull 6
#define FStar_Pervasives_Iota 7
#define FStar_Pervasives_NBE 8
#define FStar_Pervasives_Reify 9
#define FStar_Pervasives_UnfoldOnly 10
#define FStar_Pervasives_UnfoldFully 11
#define FStar_Pervasives_UnfoldAttr 12

typedef uint8_t FStar_Pervasives_norm_step_tags;

typedef struct FStar_Pervasives_norm_step_s
{
  FStar_Pervasives_norm_step_tags tag;
  union {
    Prims_list__Prims_string *case_UnfoldOnly;
    Prims_list__Prims_string *case_UnfoldFully;
    Prims_list__Prims_string *case_UnfoldAttr;
  }
  ;
}
FStar_Pervasives_norm_step;

extern bool FStar_Pervasives_uu___is_Simpl(FStar_Pervasives_norm_step projectee);

extern bool FStar_Pervasives_uu___is_Weak(FStar_Pervasives_norm_step projectee);

extern bool FStar_Pervasives_uu___is_HNF(FStar_Pervasives_norm_step projectee);

extern bool FStar_Pervasives_uu___is_Primops(FStar_Pervasives_norm_step projectee);

extern bool FStar_Pervasives_uu___is_Delta(FStar_Pervasives_norm_step projectee);

extern bool FStar_Pervasives_uu___is_Zeta(FStar_Pervasives_norm_step projectee);

extern bool FStar_Pervasives_uu___is_ZetaFull(FStar_Pervasives_norm_step projectee);

extern bool FStar_Pervasives_uu___is_Iota(FStar_Pervasives_norm_step projectee);

extern bool FStar_Pervasives_uu___is_NBE(FStar_Pervasives_norm_step projectee);

extern bool FStar_Pervasives_uu___is_Reify(FStar_Pervasives_norm_step projectee);

extern bool FStar_Pervasives_uu___is_UnfoldOnly(FStar_Pervasives_norm_step projectee);

extern Prims_list__Prims_string
*FStar_Pervasives___proj__UnfoldOnly__item___0(FStar_Pervasives_norm_step projectee);

extern bool FStar_Pervasives_uu___is_UnfoldFully(FStar_Pervasives_norm_step projectee);

extern Prims_list__Prims_string
*FStar_Pervasives___proj__UnfoldFully__item___0(FStar_Pervasives_norm_step projectee);

extern bool FStar_Pervasives_uu___is_UnfoldAttr(FStar_Pervasives_norm_step projectee);

extern Prims_list__Prims_string
*FStar_Pervasives___proj__UnfoldAttr__item___0(FStar_Pervasives_norm_step projectee);

extern FStar_Pervasives_norm_step FStar_Pervasives_simplify;

extern FStar_Pervasives_norm_step FStar_Pervasives_weak;

extern FStar_Pervasives_norm_step FStar_Pervasives_hnf;

extern FStar_Pervasives_norm_step FStar_Pervasives_primops;

extern FStar_Pervasives_norm_step FStar_Pervasives_delta;

extern FStar_Pervasives_norm_step FStar_Pervasives_zeta;

extern FStar_Pervasives_norm_step FStar_Pervasives_zeta_full;

extern FStar_Pervasives_norm_step FStar_Pervasives_iota;

extern FStar_Pervasives_norm_step FStar_Pervasives_nbe;

extern FStar_Pervasives_norm_step FStar_Pervasives_reify_;

extern FStar_Pervasives_norm_step FStar_Pervasives_delta_only(Prims_list__Prims_string *s);

extern FStar_Pervasives_norm_step FStar_Pervasives_delta_fully(Prims_list__Prims_string *s);

extern FStar_Pervasives_norm_step FStar_Pervasives_delta_attr(Prims_list__Prims_string *s);

typedef struct Prims_list__FStar_Pervasives_norm_step_s Prims_list__FStar_Pervasives_norm_step;

typedef struct Prims_list__FStar_Pervasives_norm_step_s
{
  Prims_list__bool_tags tag;
  FStar_Pervasives_norm_step hd;
  Prims_list__FStar_Pervasives_norm_step *tl;
}
Prims_list__FStar_Pervasives_norm_step;

extern void
*FStar_Pervasives_norm(Prims_list__FStar_Pervasives_norm_step *uu____2438, void *uu____2439);

#define __FStar_Pervasives_H_DEFINED
#endif
