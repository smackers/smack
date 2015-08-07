//
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "simple.h"

void test(int a) {
  int b = a;

  a = incr(a);
  assert(a > b);
}

void test2() {
  char* s1 = "1string";
  assert(s1!=retStr());

}

int main(void) {
  int a = __VERIFIER_nondet();
  assume(a < 10000); // prevents overflow when bit-precise
  test(a);
  test2();
  return 0;
}

