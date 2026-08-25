// This file is distributed under the MIT License. See LICENSE for details.
// A literal -1 is passed as a call argument. Inside the callee the parameter
// is stored through a pointer (signed consumer via memory) and divided as
// unsigned. The store must keep the literal signed at the call site.
// @expect verified
// @flag --sign-analysis
#include "smack.h"

unsigned sink;

void chk(unsigned p, int *out) {
  *out = (int)p;
  sink = p / 2u;
}

int main(void) {
  int o = 0;
  chk(-1, &o);
  __VERIFIER_assert(o < 0);
  return 0;
}
