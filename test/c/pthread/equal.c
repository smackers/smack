#include "smack.h"
#include <assert.h>
#include <pthread.h>

// Tests pthread_equal()
// @expect verified

pthread_t worker;

void *t1(void *arg) {
  assert(pthread_equal(pthread_self(), worker));
  return 0;
}

int main(void) {
  pthread_create(&worker, 0, 0, 0);
  pthread_join(worker, 0);
  assert(!pthread_equal(pthread_self(), worker));
  return 0;
}
