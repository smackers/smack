// This file is distributed under the MIT License. See LICENSE for details.
// An unsigned nondeterministic value compared for equality against UINT_MAX
// with no other consumer. The value lives in [0, 2^32) (its producer fixes
// the window), so the equality literal must be readable in that window: when
// the analysis has no evidence it must not commit to the signed spelling.
// @expect verified
// @flag --sign-analysis
#include "smack.h"
#include <limits.h>

int main(void) {
  unsigned x = __VERIFIER_nondet_uint();
  if (x != UINT_MAX)
    __VERIFIER_assert(x < UINT_MAX);
  return 0;
}
