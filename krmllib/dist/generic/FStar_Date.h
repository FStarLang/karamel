/*
  Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
  Licensed under the Apache 2.0 License.
*/


#ifndef __FStar_Date_H
#define __FStar_Date_H




#include <inttypes.h>
#include "krmllib.h"
#include "krml/internal/compat.h"
#include "krml/internal/target.h"
extern FStar_Date_dateTime FStar_Date_now();

extern Prims_int FStar_Date_secondsFromDawn();

extern FStar_Date_timeSpan
FStar_Date_newTimeSpan(Prims_int uu___, Prims_int uu___1, Prims_int uu___2, Prims_int uu___3);

extern FStar_Date_dateTime
FStar_Date_addTimeSpan(FStar_Date_dateTime uu___, FStar_Date_timeSpan uu___1);

extern bool FStar_Date_greaterDateTime(FStar_Date_dateTime uu___, FStar_Date_dateTime uu___1);


#define __FStar_Date_H_DEFINED
#endif
