// This file is distributed under the MIT License. See LICENSE for details.
// Failing twin of sign_analysis_memory.c: g is -1, so g >= 0 fails.
// @expect error
// @flag --sign-analysis
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
  __VERIFIER_assert(g >= 0);
  return (int)q;
}
