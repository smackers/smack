// This file is distributed under the MIT License. See LICENSE for details.
// A store through an integer-cast pointer into a global. The sanitizer
// scaffolding turns `(unsigned long)&g + 4` into checked arithmetic; the
// cleanup that removes it must not fold the pointer into a constant
// expression that sea-dsa no longer links to g, or the store lands in a
// different memory region than the direct read of g.b.
// @expect verified
// @flag --sign-analysis
#include "smack.h"

struct S {
  int a;
  int b;
} g;

int main(void) {
  unsigned long tmp = (unsigned long)&g + 4;
  int *pb = (int *)tmp;
  g.b = 7;
  *pb = 5;
  __VERIFIER_assert(g.b == 5);
  return 0;
}
