// This file is distributed under the MIT License. See LICENSE for details.
// Failing twin of sign_analysis_phi.c: the sentinel branch is reachable, so
// the equality must not be rendered unsatisfiable.
// @expect error
// @flag --sign-analysis
#include "smack.h"
#include <limits.h>

int main(void) {
  unsigned u;
  if (__VERIFIER_nondet_int())
    u = UINT_MAX;
  else
    u = 0;
  unsigned q = u / 3;
  if (u == UINT_MAX)
    __VERIFIER_assert(u == 0);
  return (int)q;
}
