// This file is distributed under the MIT License. See LICENSE for details.
// Failing twin of sign_analysis_call_arg.c: o is -1, so o >= 0 fails.
// @expect error
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
  __VERIFIER_assert(o >= 0);
  return 0;
}
