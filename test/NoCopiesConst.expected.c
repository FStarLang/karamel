/* krml header omitted for test repeatability */


#include "NoCopiesConst.h"

#include "Steel_SpinLock.h"

void NoCopiesConst_forward(Steel_SpinLock_s_lock *x)
{
  Steel_SpinLock_acquire(x);
}

void NoCopiesConst_forward_twice(Steel_SpinLock_s_lock *x)
{
  NoCopiesConst_forward(x);
  NoCopiesConst_forward(x);
}

void NoCopiesConst_acquire_nested(NoCopiesConst_nested_lock *x)
{
  Steel_SpinLock_acquire(&x->inner.lock);
}

void NoCopiesConst_forward_nested(NoCopiesConst_nested_lock *x)
{
  NoCopiesConst_acquire_nested(x);
}

uint32_t NoCopiesConst_read_plain(NoCopiesConst_plain x)
{
  return x.left;
}

uint32_t NoCopiesConst_forward_plain(NoCopiesConst_plain x)
{
  return NoCopiesConst_read_plain(x);
}

