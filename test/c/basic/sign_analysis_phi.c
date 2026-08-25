// This file is distributed under the MIT License. See LICENSE for details.
// A UINT_MAX sentinel enters a phi whose result has an unsigned consumer
// (udiv). The literal inside the equality must be printed in the same window
// as the phi incoming literal; otherwise `u != UINT_MAX` is a tautology under
// the unbounded integer encoding and the assertion is a false alarm.
// @expect verified
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
  if (u != UINT_MAX)
    __VERIFIER_assert(u == 0);
  return (int)q;
}
