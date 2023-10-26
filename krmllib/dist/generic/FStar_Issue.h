/*
  Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
  Licensed under the Apache 2.0 License.
*/


#ifndef __FStar_Issue_H
#define __FStar_Issue_H

#include "FStar_String.h"
#include "FStar_Bytes.h"
#include "FStar_BitVector.h"
#include <inttypes.h>
#include "krmllib.h"
#include "krml/internal/compat.h"
#include "krml/internal/target.h"

typedef Prims_string FStar_Issue_issue_level_string;

typedef struct Prims_list__FStar_Pprint_document_s Prims_list__FStar_Pprint_document;

typedef struct Prims_list__FStar_Pprint_document_s
{
  Prims_list__bool_tags tag;
  FStar_Pprint_document hd;
  Prims_list__FStar_Pprint_document *tl;
}
Prims_list__FStar_Pprint_document;

extern Prims_list__FStar_Pprint_document *FStar_Issue_message_of_issue(FStar_Issue_issue i);

extern Prims_string FStar_Issue_level_of_issue(FStar_Issue_issue i);

typedef struct FStar_Pervasives_Native_option__krml_checked_int_t_s
{
  FStar_Pervasives_Native_option__Prims_string_tags tag;
  krml_checked_int_t v;
}
FStar_Pervasives_Native_option__krml_checked_int_t;

extern FStar_Pervasives_Native_option__krml_checked_int_t
FStar_Issue_number_of_issue(FStar_Issue_issue i);

extern FStar_Pervasives_Native_option__FStar_Range_range
FStar_Issue_range_of_issue(FStar_Issue_issue i);

extern Prims_list__Prims_string *FStar_Issue_context_of_issue(FStar_Issue_issue i);

extern Prims_string FStar_Issue_render_issue(FStar_Issue_issue i);

extern FStar_Issue_issue
FStar_Issue_mk_issue_doc(
  Prims_string i,
  Prims_list__FStar_Pprint_document *msg,
  FStar_Pervasives_Native_option__FStar_Range_range range,
  FStar_Pervasives_Native_option__krml_checked_int_t number,
  Prims_list__Prims_string *ctx
);


#define __FStar_Issue_H_DEFINED
#endif
