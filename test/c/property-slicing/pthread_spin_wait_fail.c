#include "smack.h"
#include <assert.h>
#include <pthread.h>

// @expect error
// @flag --pthread
// @flag --context-bound=2

// The failing twin of pthread_spin_wait.c: the producer publishes `flag`
// before `x`, so waiting for the flag no longer establishes anything about x.
// It keeps the "verified" verdict of the twin honest -- the assertion is
// reachable and checked, not folded away.

int flag = 0;
int x = 0;

void *producer(void *arg) {
  flag = 1;
  x = 1;
  return 0;
}

int main(void) {
  pthread_t t;
  pthread_create(&t, 0, producer, 0);
  while (flag == 0) {
  }
  assert(x == 1);
  return 0;
}
