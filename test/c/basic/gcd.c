// This test shows why we need parallel assignment when translating Phi nodes
#include "smack.h"
#include <assert.h>

// @expect verified

int gcd_test(int a, int b) {
  int t;

  if (a < 0)
    a = -a;
  if (b < 0)
    b = -b;

  while (b != 0) {
    t = b;
    b = a % b;
    a = t;
  }
  return a;
}

int main(void) {
  int x = __VERIFIER_nondet_int();
  int y = __VERIFIER_nondet_int();
  int g;

  if (y > 0 && x > 0 && x % y == 0) {
    g = gcd_test(x, y);
    assert(g == y);
  }

  return 0;
}
