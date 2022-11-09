#include "Steel_SpinLock.h"
#include <pthread.h>

Steel_SpinLock_lock_t Steel_SpinLock_new_lock () {
  pthread_mutex_t mutex;
  int rc = pthread_mutex_init(&mutex, NULL);
  assert (rc = 0);
  return mutex;
}

void Steel_SpinLock_acquire(Steel_SpinLock_lock_t l) {
  pthread_mutex_lock(&l); 
}

void Steel_SpinLock_release(Steel_SpinLock_lock_t l) {
  pthread_mutex_unlock(&l);
}
