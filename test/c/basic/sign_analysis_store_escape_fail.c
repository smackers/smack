// This file is distributed under the MIT License. See LICENSE for details.
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
  unsigned u = f(__VERIFIER_nondet_int());
  unsigned q = u / 3;
  if (g < 0)
    __VERIFIER_assert(0);
  return (int)q;
}
