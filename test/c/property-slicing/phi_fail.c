#include "smack.h"
#include <assert.h>

// @expect error
// A PHI feeding the assertion: every incoming value stays relevant.

int main(void) {
  int x;
  if (__VERIFIER_nondet_int()) {
    x = 1;
  } else {
    x = 2;
  }
  assert(x != 2);
  return 0;
}
