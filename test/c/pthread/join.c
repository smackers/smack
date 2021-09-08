#include "smack.h"
#include <assert.h>
#include <pthread.h>

// Shows pthread_join effectively blocks until child thread done
// @expect verified

int x = 1;

void *t1(void *arg) {
  x++;
  pthread_exit(0);
  return 0;
}

int main(void) {
  pthread_t t;

  pthread_create(&t, 0, t1, 0);
  pthread_join(t, 0);
  x++;
  assert(x == 3);
  return 0;
}
