//
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "simple.h"

void test(int a) {
  int b = a;

  a = incr(a);
  assert(a > b);
}

int main(void) {
  int a = __SMACK_nondet();
  test(a);
  return 0;
}

