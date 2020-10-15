#include "smack.h"
#include <assert.h>
#include <pthread.h>

// Tests failure on use of uninitialized mutex
// @expect error

int z = 1;

void *t1(void *arg) {
  pthread_mutex_t *lock = arg;
  pthread_mutex_lock(lock);
  z++;
  pthread_mutex_unlock(lock);
  return 0;
}

int main(void) {
  pthread_mutex_t lock;
  pthread_t tid1;

  pthread_create(&tid1, 0, t1, &lock);
  pthread_mutex_lock(&lock);
  z++;
  pthread_mutex_unlock(&lock);
  pthread_join(tid1, 0);
  assert(z == 3);
  return 0;
}
