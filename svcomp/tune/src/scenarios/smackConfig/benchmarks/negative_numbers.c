#include "smack.h"

// @flag --unroll=2
// @expect verified

int incr(int x) {
  return x + 1;
}

int main(void) {
  int a = -11;
  a = incr(a);
  assert(a == -10);
  return 0;
}

