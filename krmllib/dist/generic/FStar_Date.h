/*
  Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
  Licensed under the Apache 2.0 and MIT Licenses.
*/


#ifndef __FStar_Date_H
#define __FStar_Date_H

#include <inttypes.h>
#include "krmllib.h"
#include "krml/internal/compat.h"
#include "krml/internal/target.h"

extern FStar_Date_dateTime FStar_Date_now(void);

extern krml_checked_int_t FStar_Date_secondsFromDawn(void);

extern FStar_Date_timeSpan
FStar_Date_newTimeSpan(
  krml_checked_int_t uu___,
  krml_checked_int_t uu___1,
  krml_checked_int_t uu___2,
  krml_checked_int_t uu___3
);

extern FStar_Date_dateTime
FStar_Date_addTimeSpan(FStar_Date_dateTime uu___, FStar_Date_timeSpan uu___1);

extern bool FStar_Date_greaterDateTime(FStar_Date_dateTime uu___, FStar_Date_dateTime uu___1);


#define __FStar_Date_H_DEFINED
#endif
