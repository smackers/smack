// This file is distributed under the MIT License. See LICENSE for details.
// Failing twin of sign_analysis_ret.c: u is UINT_MAX, so u <= 100 fails.
// @expect error
// @flag --sign-analysis
#include "smack.h"

int sentinel(void) { return -1; }

int main(void) {
  unsigned u = sentinel();
  __VERIFIER_assert(u <= 100u);
  return 0;
}
