// This file is distributed under the MIT License. See LICENSE for details.
// @expect error
// @flag --unroll=8
// clang-format off
// @flag --sign-analysis --clang-options=-fno-sanitize=signed-integer-overflow,unsigned-integer-overflow
// clang-format on

#include "smack.h"
#include <assert.h>

int main(void) {
  unsigned n = __VERIFIER_nondet_unsigned();
  __VERIFIER_assume(n == 5);
  unsigned count = 0;
  for (unsigned i = n; i > 0; i--)
    count++;
  assert(count == 4);
  return 0;
}
