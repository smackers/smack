// This file is distributed under the MIT License. See LICENSE for details.
// Failing twin of sign_analysis_conflict.c: a can be -1, so a >= 0 fails.
// Rendering the Conflict literal unsigned would hide this bug.
// @expect error
// @flag --sign-analysis
#include "smack.h"

int f(int c) {
  int r;
  if (c)
    r = -1;
  else
    r = 5;
  return r;
}

int main(void) {
  int a = f(__VERIFIER_nondet_int());
  unsigned b = f(__VERIFIER_nondet_int());
  if (b > 100u)
    b = 100u;
  __VERIFIER_assert(a >= 0);
  return (int)b;
}
