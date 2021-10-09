#include "smack.h"
#include <assert.h>
#include <pthread.h>

// Tests deadlock detection when join on self
// @expect verified

pthread_mutex_t lock = PTHREAD_MUTEX_INITIALIZER;

void *t1(void *arg) {
  pthread_t *selfptr = (pthread_t *)arg;
  pthread_t self = *selfptr;
  int ret;
  int err = pthread_join(self, (void *)&ret);
  // Should be an EDEADLK error
  assert(err == 35);
  pthread_exit((void *)1);
  return 0;
}

int main(void) {
  pthread_t tid1 = __VERIFIER_nondet_int();
  int ret;
  pthread_create(&tid1, 0, t1, &tid1);
  return 0;
}
