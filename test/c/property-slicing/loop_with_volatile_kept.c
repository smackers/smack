#include "smack.h"
#include <assert.h>

// @expect verified
// A volatile access is an effect the region abstraction does not model, so the
// loop must be retained regardless of relevance.

int main(void) {
  volatile int reg = 0;
  int i;
  int watched = 1;
  for (i = 0; i < 4; i++) {
    reg = i;
  }
  assert(watched == 1);
  return 0;
}
