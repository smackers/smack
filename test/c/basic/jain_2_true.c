#include "smack.h"
#include <assert.h>

// @expect verified

int main(void) {
  int x = 1, y = 1;

  while (1) {
    x = x + 2 * __VERIFIER_nondet_int();
    y = y + 2 * __VERIFIER_nondet_int();
    assert(x + y != 1);
  }
  return 0;
}
