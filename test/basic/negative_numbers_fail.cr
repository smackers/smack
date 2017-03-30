#include "smack.h"

// @expect error

int incr(int x) {
  return x + 1;
}

int main(void) {
  int a = -11;
  a = incr(a);
  assert(a == 12);
  return 0;
}

