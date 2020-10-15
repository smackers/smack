#include "smack.h"
#include <assert.h>
#include <pthread.h>

// Ensures return values from multiple threads can be
// held simultaneously.
// @expect verified

int x = 1;

void *t1(void *arg) {
  x++;
  pthread_exit((void *)5);
  return 0;
}

void *t2(void *arg) {
  x++;
  pthread_exit((void *)6);
  return 0;
}

int main(void) {
  pthread_t tid1, tid2;
  int a;
  void *ret1, *ret2;

  pthread_create(&tid1, 0, t1, 0);
  pthread_create(&tid2, 0, t2, 0);
  pthread_join(tid1, &ret1);
  pthread_join(tid2, &ret2);
  assert((int)ret1 == 5);
  assert((int)ret2 == 6);
  return 0;
}
