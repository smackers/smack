#include "smack.h"
#include <pthread.h>
#include <stdatomic.h>
#include <stdio.h>
#include <stdlib.h>

// @expect verified
// https://github.com/smackers/smack/issues/525

_Atomic(atomic_int *) x;

void *t1(void *arg) {
  atomic_store_explicit(&x, (_Atomic(int) *)calloc(1, sizeof(int)),
                        memory_order_relaxed);
  if (atomic_load_explicit(&x, memory_order_relaxed)) {
    atomic_store_explicit(x, 42, memory_order_relaxed);
  }
  return NULL;
}

int main(void) {
  atomic_init(&x, NULL);
  pthread_t tid1;
  pthread_create(&tid1, 0, t1, 0);
  if (atomic_load_explicit(&x, memory_order_relaxed)) {
    int r1 = atomic_load_explicit(x, memory_order_relaxed);
    assert(r1 == 0 || r1 == 42);
  }
  pthread_join(tid1, 0);
  if (x) {
    free(x);
  }
  return 0;
}
