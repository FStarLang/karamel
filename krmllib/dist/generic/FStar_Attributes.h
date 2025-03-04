/*
  Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
  Licensed under the Apache 2.0 and MIT Licenses.
*/


#ifndef __FStar_Attributes_H
#define __FStar_Attributes_H

#include <inttypes.h>
#include "krmllib.h"
#include "krml/internal/compat.h"
#include "krml/internal/target.h"

#define FStar_Attributes_PpxDerivingShow 0
#define FStar_Attributes_PpxDerivingShowConstant 1
#define FStar_Attributes_PpxDerivingYoJson 2
#define FStar_Attributes_CInline 3
#define FStar_Attributes_Substitute 4
#define FStar_Attributes_Gc 5
#define FStar_Attributes_Comment 6
#define FStar_Attributes_CPrologue 7
#define FStar_Attributes_CEpilogue 8
#define FStar_Attributes_CConst 9
#define FStar_Attributes_CCConv 10
#define FStar_Attributes_CAbstractStruct 11
#define FStar_Attributes_CIfDef 12
#define FStar_Attributes_CMacro 13
#define FStar_Attributes_CNoInline 14

typedef uint8_t FStar_Attributes___internal_ocaml_attributes_tags;

typedef struct FStar_Attributes___internal_ocaml_attributes_s
{
  FStar_Attributes___internal_ocaml_attributes_tags tag;
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
FStar_Attributes___internal_ocaml_attributes;

bool
FStar_Attributes_uu___is_PpxDerivingShow(
  FStar_Attributes___internal_ocaml_attributes projectee
);

bool
FStar_Attributes_uu___is_PpxDerivingShowConstant(
  FStar_Attributes___internal_ocaml_attributes projectee
);

bool
FStar_Attributes_uu___is_PpxDerivingYoJson(
  FStar_Attributes___internal_ocaml_attributes projectee
);

bool FStar_Attributes_uu___is_CInline(FStar_Attributes___internal_ocaml_attributes projectee);

bool
FStar_Attributes_uu___is_Substitute(FStar_Attributes___internal_ocaml_attributes projectee);

bool FStar_Attributes_uu___is_Gc(FStar_Attributes___internal_ocaml_attributes projectee);

bool FStar_Attributes_uu___is_Comment(FStar_Attributes___internal_ocaml_attributes projectee);

bool
FStar_Attributes_uu___is_CPrologue(FStar_Attributes___internal_ocaml_attributes projectee);

bool
FStar_Attributes_uu___is_CEpilogue(FStar_Attributes___internal_ocaml_attributes projectee);

bool FStar_Attributes_uu___is_CConst(FStar_Attributes___internal_ocaml_attributes projectee);

bool FStar_Attributes_uu___is_CCConv(FStar_Attributes___internal_ocaml_attributes projectee);

bool
FStar_Attributes_uu___is_CAbstractStruct(
  FStar_Attributes___internal_ocaml_attributes projectee
);

bool FStar_Attributes_uu___is_CIfDef(FStar_Attributes___internal_ocaml_attributes projectee);

bool FStar_Attributes_uu___is_CMacro(FStar_Attributes___internal_ocaml_attributes projectee);

bool
FStar_Attributes_uu___is_CNoInline(FStar_Attributes___internal_ocaml_attributes projectee);


#define __FStar_Attributes_H_DEFINED
#endif
