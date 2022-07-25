/*
  Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
  Licensed under the Apache 2.0 License.
*/


#ifndef __FStar_List_Tot_Base_H
#define __FStar_List_Tot_Base_H




#include <inttypes.h>
#include "krmllib.h"
#include "krml/internal/compat.h"
#include "krml/internal/target.h"
typedef void *FStar_List_Tot_Base_memP;

typedef void *FStar_List_Tot_Base_no_repeats_p;

typedef void *FStar_List_Tot_Base_strict_suffix_of;

KRML_DEPRECATED("This function was misnamed: Please use 'strict_suffix_of'")

typedef void *FStar_List_Tot_Base_strict_prefix_of;


#define __FStar_List_Tot_Base_H_DEFINED
#endif
