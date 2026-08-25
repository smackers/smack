// This file is distributed under the MIT License. See LICENSE for details.
// `m += -1` on an unsigned is a "u"-tagged `add i32 %m, -1` under the
// sanitizer scaffolding. The tag is correct source-level information, but the
// unbounded encoding cannot represent the wrapping add it denotes: the
// arithmetic operand must be rendered as -1, not 4294967295, for m == n - 1.
// @expect verified
// @flag --sign-analysis
#include "smack.h"

int main(void) {
  unsigned n = __VERIFIER_nondet_uint();
  __VERIFIER_assume(n >= 1 && n <= 10);
  unsigned m = n;
  m += -1;
  __VERIFIER_assert(m == n - 1);
  return 0;
}
