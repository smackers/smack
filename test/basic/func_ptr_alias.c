#include "smack.h"

// @expect verified

int __incr(int x) {
  return x + 1;
}

int incr(int) __attribute__((alias ("__incr")));

int main(void) {
  int x = __VERIFIER_nondet_int();
  int y = x;
  x = incr(x);
  assert(x == y + 1);
  return 0;
}

