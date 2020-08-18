/*
  Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
  Licensed under the Apache 2.0 License.
*/


#ifndef __FStar_String_H
#define __FStar_String_H
#include <inttypes.h>
#include "kremlib.h"
#include "kremlin/internal/compat.h"
#include "kremlin/internal/target.h"


#include "FStar_BitVector.h"

typedef FStar_Char_char FStar_String_char;

typedef struct Prims_list__FStar_Char_char_s Prims_list__FStar_Char_char;

typedef struct Prims_list__FStar_Char_char_s
{
  Prims_list__bool_tags tag;
  FStar_Char_char hd;
  Prims_list__FStar_Char_char *tl;
}
Prims_list__FStar_Char_char;

extern Prims_list__FStar_Char_char *FStar_String_list_of_string(Prims_string uu____9);

extern Prims_string FStar_String_string_of_list(Prims_list__FStar_Char_char *uu____21);

extern Prims_int FStar_String_strlen(Prims_string s);

extern Prims_int FStar_String_length(Prims_string s);

extern Prims_string FStar_String_make(Prims_int l, FStar_Char_char uu____61);

extern Prims_string FStar_String_string_of_char(FStar_Char_char c);

typedef struct Prims_list__Prims_string_s Prims_list__Prims_string;

typedef struct Prims_list__Prims_string_s
{
  Prims_list__bool_tags tag;
  Prims_string hd;
  Prims_list__Prims_string *tl;
}
Prims_list__Prims_string;

extern Prims_list__Prims_string
*FStar_String_split(Prims_list__FStar_Char_char *uu____86, Prims_string uu____87);

extern Prims_string
FStar_String_concat(Prims_string uu____108, Prims_list__Prims_string *uu____109);

extern Prims_int FStar_String_compare(Prims_string uu____126, Prims_string uu____127);

extern Prims_string FStar_String_lowercase(Prims_string uu____135);

extern Prims_string FStar_String_uppercase(Prims_string uu____143);

extern FStar_Char_char FStar_String_index(Prims_string s, Prims_int n);

extern Prims_int FStar_String_index_of(Prims_string uu____174, FStar_Char_char uu____175);

extern Prims_string FStar_String_sub(Prims_string s, Prims_int i, Prims_int l);

KRML_DEPRECATED("FStar.String.collect can be defined using list_of_string and List.collect")

extern Prims_string
FStar_String_collect(Prims_string (*uu____218)(FStar_Char_char x0), Prims_string uu____219);

extern Prims_string
FStar_String_substring(Prims_string uu____243, Prims_int uu____244, Prims_int uu____245);

extern FStar_Char_char FStar_String_get(Prims_string uu____260, Prims_int uu____261);


#define __FStar_String_H_DEFINED
#endif
