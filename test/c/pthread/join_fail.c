#include "smack.h"
#include <assert.h>
#include <pthread.h>

// Shows join.c fails when parent doesn't wait for child before x++ call
// @expect error

int x = 1;

void *t1(void *arg) {
  x++;
  pthread_exit(0);
  return 0;
}

int main(void) {
  pthread_t t;

  pthread_create(&t, 0, t1, 0);
  x++;
  pthread_join(t, 0);
  assert(x == 3);
  return 0;
}
