#include "smack.h"
#include <assert.h>

// @expect verified
// A scalar computation nothing relevant reads must be removable without
// changing the verdict.

int main(void) {
  int a = __VERIFIER_nondet_int();
  int dead = a * 3 + 7;
  dead = dead ^ (dead << 2);
  int b = 1;
  assert(b == 1);
  return 0;
}
