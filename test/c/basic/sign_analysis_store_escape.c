// This file is distributed under the MIT License. See LICENSE for details.
// @expect verified
// @flag --sign-analysis
// @checkbpl grep -F '$i2 := $sub.i32(0, 1);'

// The phi literal -1 in f is returned to a caller whose only SSA-visible
// consumer is unsigned, but it is also stored to g and read back by a signed
// compare. A store is a consumer the analysis cannot see through, so the
// value escapes and keeps the signed spelling instead of becoming
// 4294967295, which would make `g >= 0` reachable.

#include "smack.h"

int g;

int f(int c) {
  int r;
  if (c)
    r = -1;
  else
    r = 0;
  g = r;
  return r;
}

int main(void) {
  int c = __VERIFIER_nondet_int();
  __VERIFIER_assume(c != 0);
  unsigned u = f(c);
  unsigned q = u / 3;
  if (g >= 0)
    __VERIFIER_assert(0);
  return (int)q;
}
