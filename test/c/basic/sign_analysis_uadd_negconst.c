// This file is distributed under the MIT License. See LICENSE for details.
// @expect verified
// @flag --sign-analysis
// @checkbpl grep -F '$add.i32($i0, $sub.i32(0, 1))'

// The sanitizer lowers `x + UINT_MAX` to `add i32 %x, -1` tagged "u". The tag
// describes the window of the value, not the spelling of the operand: the
// add does not wrap under the integer encoding, so only `x + (-1)` yields the
// C result 4.

#include "smack.h"
#include <limits.h>

int main(void) {
  unsigned x = __VERIFIER_nondet_uint();
  __VERIFIER_assume(x == 5);
  unsigned y = x + UINT_MAX;
  if (y != 4)
    __VERIFIER_assert(0);
  return 0;
}
