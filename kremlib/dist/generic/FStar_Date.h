/*
  Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
  Licensed under the Apache 2.0 License.
*/

#include <inttypes.h>
#include "kremlib.h"
#include "kremlin/internal/compat.h"
#include "kremlin/internal/target.h"

#ifndef __FStar_Date_H
#define __FStar_Date_H




extern FStar_Date_dateTime FStar_Date_now();

extern Prims_int FStar_Date_secondsFromDawn();

extern FStar_Date_timeSpan
FStar_Date_newTimeSpan(
  Prims_int uu____52,
  Prims_int uu____53,
  Prims_int uu____54,
  Prims_int uu____55
);

extern FStar_Date_dateTime
FStar_Date_addTimeSpan(FStar_Date_dateTime uu____76, FStar_Date_timeSpan uu____77);

extern bool
FStar_Date_greaterDateTime(FStar_Date_dateTime uu____95, FStar_Date_dateTime uu____96);

#define __FStar_Date_H_DEFINED
#endif
