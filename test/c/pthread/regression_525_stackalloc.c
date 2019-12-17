#include "smack.h"
#include <pthread.h>
#include <stdlib.h>

// @expect verified
// https://github.com/smackers/smack/issues/525

struct atomic_var {
  void *value;
};

struct S {
  struct atomic_var x;
  struct atomic_var y;
};

struct T {
  int z;
};

void atomic_store_ptr(struct atomic_var *var, void *p) {
  __atomic_store_n(&var->value, p, __ATOMIC_SEQ_CST);
}

void *foo(void *arg) {
  struct T t = *(struct T *)arg;
  return NULL;
}

int main(void) {
  struct S s;
  struct T t;
  pthread_t thread;

  (*(size_t *)(&s.x.value)) = 0;
  s.y.value = NULL;

  if (pthread_create(&thread, NULL, foo, (void *)&t))
    return 1;

  uint64_t v = (size_t)s.x.value;
  atomic_store_ptr(&s.y, NULL);
  uint64_t w = (size_t)s.x.value;
  assert(v == w);
  return 0;
}
