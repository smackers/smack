// This file is distributed under the MIT License. See LICENSE for details.
// A literal -1 is returned from a function whose only call result consumer is
// an unsigned comparison. The return rule follows the call edge, so the
// literal is printed in the unsigned window and UINT_MAX > 100 holds.
// @expect verified
// @flag --sign-analysis
#include "smack.h"

int sentinel(void) { return -1; }

int main(void) {
  unsigned u = sentinel();
  __VERIFIER_assert(u > 100u);
  return 0;
}
