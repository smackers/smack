#include "smack.h"
#include <assert.h>

// @expect error
// A chain of SSA definitions reaching the assertion must be retained.

int main(void) {
  int a = __VERIFIER_nondet_int();
  __VERIFIER_assume(a == 4);
  int b = a + 1;
  int c = b * 2;
  int d = c - 3;
  assert(d != 7);
  return 0;
}
