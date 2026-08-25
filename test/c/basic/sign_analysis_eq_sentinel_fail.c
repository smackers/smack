// This file is distributed under the MIT License. See LICENSE for details.
// @expect error
// @flag --sign-analysis
// @checkbpl grep -F '$i2 := 4294967295;'
// @checkbpl grep -F '$eq.i32($i2, 4294967295)'

// The phi literal takes the unsigned window because of the udiv; the
// equality literal must follow it or `u == UINT_MAX` is never true.

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
    __VERIFIER_assert(0);
  return (int)q;
}
