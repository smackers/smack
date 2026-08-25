// This file is distributed under the MIT License. See LICENSE for details.
// @expect error
// @flag --sign-analysis
// clang-format off
// @checkbpl grep -F '(if ($eq.i32.bool($i0, $sub.i32(0, 1)) || $eq.i32.bool($i0, 4294967295)) then 1 else 0)'
// clang-format on

// Nothing but the equality consumes x, so its window is unknown. The literal
// is then compared against both representatives of its bit pattern, which is
// exact under the integer encoding and lets the sentinel test succeed for the
// non-negative x that __VERIFIER_nondet_uint() produces.

#include "smack.h"
#include <limits.h>

int main(void) {
  unsigned x = __VERIFIER_nondet_uint();
  if (x == UINT_MAX)
    __VERIFIER_assert(0);
  return 0;
}
