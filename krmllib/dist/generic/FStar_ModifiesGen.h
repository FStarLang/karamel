/*
  Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
  Licensed under the Apache 2.0 License.
*/


#ifndef __FStar_ModifiesGen_H
#define __FStar_ModifiesGen_H

#include <inttypes.h>
#include "krmllib.h"
#include "krml/internal/compat.h"
#include "krml/internal/target.h"

typedef void *FStar_ModifiesGen_aloc_t;

#define FStar_ModifiesGen_Loc 0

typedef uint8_t FStar_ModifiesGen_loc_;

typedef FStar_ModifiesGen_loc_ FStar_ModifiesGen_loc;

typedef void *FStar_ModifiesGen_loc_includes;

typedef void *FStar_ModifiesGen_loc_disjoint;

typedef void *FStar_ModifiesGen_modifies;

typedef void *FStar_ModifiesGen_does_not_contain_addr;


#define __FStar_ModifiesGen_H_DEFINED
#endif
