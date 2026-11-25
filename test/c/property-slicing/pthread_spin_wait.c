#include "smack.h"
#include <assert.h>
#include <pthread.h>

// @expect verified
// @flag --pthread
// @flag --context-bound=2

// The slicer must refuse concurrent programs. `flag` is the release side of a
// handshake: the spin loop below carries no *intra-thread* dependence to the
// assertion -- its body is empty, and the block after it post-dominates the
// header, so nothing is control-dependent on the exit test -- yet it is the
// only thing that orders `x = 1` before `assert(x == 1)`. Slicing this program
// bypasses the loop and reports a spurious error.

int flag = 0;
int x = 0;

void *producer(void *arg) {
  x = 1;
  flag = 1;
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
