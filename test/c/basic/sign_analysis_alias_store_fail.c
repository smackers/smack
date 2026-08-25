// This file is distributed under the MIT License. See LICENSE for details.
// Failing twin of sign_analysis_alias_store.c: the store through pb
// overwrites g.b, so g.b == 7 fails.
// @expect error
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
  __VERIFIER_assert(g.b == 7);
  return 0;
}
