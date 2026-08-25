// This file is distributed under the MIT License. See LICENSE for details.
// @expect verified
// @flag --unroll=8
// clang-format off
// @flag --sign-analysis --clang-options=-fno-sanitize=signed-integer-overflow,unsigned-integer-overflow
// @checkbpl grep -F '$add.i32($i4, $sub.i32(0, 1))'
// clang-format on

// Uninstrumented `i--` on an unsigned counter is `add i32 %i, -1` with no
// wrap flags and no metadata. The only consumer of the sum is an unsigned
// compare, but the literal must still be spelled -1: under the integer
// encoding `i + 4294967295` never reaches zero and the loop would run forever.

#include "smack.h"
#include <assert.h>

int main(void) {
  unsigned n = __VERIFIER_nondet_unsigned();
  __VERIFIER_assume(n == 5);
  unsigned count = 0;
  for (unsigned i = n; i > 0; i--)
    count++;
  assert(count == 5);
  return 0;
}
