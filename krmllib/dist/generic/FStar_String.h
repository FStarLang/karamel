/*
  Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
  Licensed under the Apache 2.0 License.
*/


#ifndef __FStar_String_H
#define __FStar_String_H



#include "FStar_BitVector.h"
#include <inttypes.h>
#include "krmllib.h"
#include "krml/internal/compat.h"
#include "krml/internal/target.h"
typedef FStar_Char_char FStar_String_char;

typedef struct Prims_list__FStar_Char_char_s Prims_list__FStar_Char_char;

typedef struct Prims_list__FStar_Char_char_s
{
  Prims_list__bool_tags tag;
  FStar_Char_char hd;
  Prims_list__FStar_Char_char *tl;
}
Prims_list__FStar_Char_char;

extern Prims_list__FStar_Char_char *FStar_String_list_of_string(Prims_string uu___);

extern Prims_string FStar_String_string_of_list(Prims_list__FStar_Char_char *uu___);

extern Prims_int FStar_String_strlen(Prims_string s);

extern Prims_int FStar_String_length(Prims_string s);

typedef void *FStar_String_maxlen;

extern Prims_string FStar_String_make(Prims_int l, FStar_Char_char uu___);

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
*FStar_String_split(Prims_list__FStar_Char_char *uu___, Prims_string uu___1);

extern Prims_string FStar_String_concat(Prims_string uu___, Prims_list__Prims_string *uu___1);

extern Prims_int FStar_String_compare(Prims_string uu___, Prims_string uu___1);

extern Prims_string FStar_String_lowercase(Prims_string uu___);

extern Prims_string FStar_String_uppercase(Prims_string uu___);

extern FStar_Char_char FStar_String_index(Prims_string s, Prims_int n);

extern Prims_int FStar_String_index_of(Prims_string uu___, FStar_Char_char uu___1);

extern Prims_string FStar_String_sub(Prims_string s, Prims_int i, Prims_int l);

KRML_DEPRECATED("FStar.String.collect can be defined using list_of_string and List.collect")

extern Prims_string
FStar_String_collect(Prims_string (*uu___)(FStar_Char_char x0), Prims_string uu___1);

extern Prims_string
FStar_String_substring(Prims_string uu___, Prims_int uu___1, Prims_int uu___2);

extern FStar_Char_char FStar_String_get(Prims_string uu___, Prims_int uu___1);


#define __FStar_String_H_DEFINED
#endif
