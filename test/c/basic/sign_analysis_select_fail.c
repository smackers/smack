// This file is distributed under the MIT License. See LICENSE for details.
// Failing twin of sign_analysis_select.c.
// @expect error
// @flag --sign-analysis
#include "smack.h"
#include <limits.h>

int main(void) {
  int c = __VERIFIER_nondet_int();
  unsigned u = c ? UINT_MAX : 0u;
  unsigned q = u / 3;
  if (u == UINT_MAX)
    __VERIFIER_assert(u == 0);
  return (int)q;
}
