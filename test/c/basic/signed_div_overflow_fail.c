// This file is distributed under the MIT License. See LICENSE for details.
// @expect error
// @flag --check=integer-overflow
// @checkbpl grep -F 'call __SMACK_check_overflow'

#include "smack.h"
#include <limits.h>

int main(void) {
  int dividend = __VERIFIER_nondet_int();
  int divisor = __VERIFIER_nondet_int();
  __VERIFIER_assume(dividend == INT_MIN);
  __VERIFIER_assume(divisor == -1);
  return dividend / divisor;
}
