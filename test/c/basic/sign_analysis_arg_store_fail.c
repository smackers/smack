// This file is distributed under the MIT License. See LICENSE for details.
// @expect error
// @flag --sign-analysis
// @checkbpl grep -F 'call chk($sub.i32(0, 1), $p0);'

// The literal -1 is passed to a parameter that is consumed by an unsigned
// division and also stored through a pointer. The store makes the parameter
// escape, so the argument keeps its signed spelling and the signed read of
// the stored value in main still sees -1.

#include "smack.h"

unsigned sink;

void chk(unsigned p, int *out) {
  *out = (int)p;
  sink = p / 2u;
}

int main(void) {
  int o = 0;
  chk(-1, &o);
  if (o < 0)
    __VERIFIER_assert(0);
  return 0;
}
