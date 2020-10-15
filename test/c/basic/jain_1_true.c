#include "smack.h"
#include <assert.h>

// @expect verified

int main(void) {
  int y = 1;

  while (1) {
    y = y + 2 * __VERIFIER_nondet_int();
    assert(y != 0);
  }
  return 0;
}
