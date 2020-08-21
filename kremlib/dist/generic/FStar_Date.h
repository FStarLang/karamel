/*
  Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
  Licensed under the Apache 2.0 License.
*/


#ifndef __FStar_Date_H
#define __FStar_Date_H
#include <inttypes.h>
#include "kremlib.h"
#include "kremlin/internal/compat.h"
#include "kremlin/internal/target.h"




extern FStar_Date_dateTime FStar_Date_now();

extern Prims_int FStar_Date_secondsFromDawn();

extern FStar_Date_timeSpan
FStar_Date_newTimeSpan(
  Prims_int uu____44,
  Prims_int uu____45,
  Prims_int uu____46,
  Prims_int uu____47
);

extern FStar_Date_dateTime
FStar_Date_addTimeSpan(FStar_Date_dateTime uu____62, FStar_Date_timeSpan uu____63);

extern bool
FStar_Date_greaterDateTime(FStar_Date_dateTime uu____78, FStar_Date_dateTime uu____79);


#define __FStar_Date_H_DEFINED
#endif
