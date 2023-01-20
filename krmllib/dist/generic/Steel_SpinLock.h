/*
  Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
  Licensed under the Apache 2.0 License.
*/


#ifndef __Steel_SpinLock_H
#define __Steel_SpinLock_H




#include <inttypes.h>
#include "krmllib.h"
#include "krml/internal/compat.h"
#include "krml/internal/target.h"
#include "krml/steel_types.h"
extern bool Steel_SpinLock_uu___is_Lock(Steel_SpinLock_lock_t projectee);

extern bool *Steel_SpinLock___proj__Lock__item__r(Steel_SpinLock_lock_t projectee);

typedef Steel_SpinLock_lock_t Steel_SpinLock_lock;

extern Steel_SpinLock_lock_t Steel_SpinLock_new_lock(void);

extern void Steel_SpinLock_acquire(Steel_SpinLock_lock_t l);

extern void Steel_SpinLock_release(Steel_SpinLock_lock_t l);

typedef Steel_SpinLock_lock_t Steel_SpinLock_s_lock;

extern Steel_SpinLock_lock_t Steel_SpinLock_new_s_lock(void);

extern void Steel_SpinLock_s_acquire(Steel_SpinLock_lock_t l);

extern void Steel_SpinLock_s_release(Steel_SpinLock_lock_t l);


#define __Steel_SpinLock_H_DEFINED
#endif
