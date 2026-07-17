#include "smack.h"
#include <assert.h>

// @expect verified

// Init functions run in the entry function's memory-region context; their
// bodies may still use memory that is not rooted at any global (here, a
// stack array). Region translation must fall back to an ordinary region
// for such values instead of aborting.

int g;

__SMACK_INIT(stack_probe) {
  int a[2];
  a[0] = 4;
  a[1] = 5;
  g = a[0] + a[1];
}

int main(void) {
  assert(g == 9);
  return 0;
}
