// This file is distributed under the MIT License. See LICENSE for details.
// Failing twin of sign_analysis_unsigned_add_neg.c.
// @expect error
// @flag --sign-analysis
#include "smack.h"

int main(void) {
  unsigned n = __VERIFIER_nondet_uint();
  __VERIFIER_assume(n >= 1 && n <= 10);
  unsigned m = n;
  m += -1;
  __VERIFIER_assert(m != n - 1);
  return 0;
}
