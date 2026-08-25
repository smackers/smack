// This file is distributed under the MIT License. See LICENSE for details.
// @expect error
// @flag --sign-analysis

#include "smack.h"
#include <limits.h>

int main(void) {
  unsigned x = __VERIFIER_nondet_uint();
  __VERIFIER_assume(x == 5);
  unsigned y = x + UINT_MAX;
  if (y == 4)
    __VERIFIER_assert(0);
  return 0;
}
