// This file is distributed under the MIT License. See LICENSE for details.
// The phi literal in f is stored to a global and returned. Its only
// SSA-visible consumer (through the return edge) is unsigned, but the memory
// consumer in main reads it as a signed int. The analysis does not follow
// memory, so a stored value must count as a conflicting consumer and keep the
// signed rendering.
// @expect verified
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
  __VERIFIER_assert(g < 0);
  return (int)q;
}
