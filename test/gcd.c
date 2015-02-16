// This test shows why we need parallel assignment when translating Phi nodes
#include "smack-defs.h"

int gcd_test(int a, int b) {
  int t;

  if (a < 0) a = -a;
  if (b < 0) b = -b;

  while (b != 0) {
    t = b;
    b = a % b;
    a = t;
  }
  return a;
}

int main(void) {
  int x = __SMACK_nondet();
  int y = __SMACK_nondet();
  int g;

  if (y > 0 && x > 0 && x % y == 0) {
    g = gcd_test(x, y);
    assert(g == y);
  }

  return 0;
}

