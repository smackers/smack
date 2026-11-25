#include "smack.h"
#include <assert.h>

// @expect error

int f(int x) { return x + 1; }

int main(void) {
  int a = __VERIFIER_nondet_int();
  __VERIFIER_assume(a == 1);
  assert(f(a) != 2);
  return 0;
}
