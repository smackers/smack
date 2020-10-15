#include "smack.h"
#include <assert.h>

// @expect verified

int main(void) {
  int x = 1;

  if (__VERIFIER_nondet_int()) {
    x++;
  } else {
    x--;
  }

  assert(x == 0 || x == 2);
  return 0;
}
