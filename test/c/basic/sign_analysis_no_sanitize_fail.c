// This file is distributed under the MIT License. See LICENSE for details.
// Failing twin of sign_analysis_no_sanitize.c: 5 - -2 is 7, not 3.
// @expect error
// @flag --sign-analysis
// clang-format off
// @flag --clang-options=-fno-sanitize=signed-integer-overflow,unsigned-integer-overflow
// clang-format on
#include "smack.h"

int signed_add(int x) { return x + -2; }

int signed_sub(int x) { return x - -2; }

int signed_mul(int x) { return x * -2; }

int main(void) {
  __VERIFIER_assert(signed_add(5) == 3);
  __VERIFIER_assert(signed_sub(5) == 3);
  __VERIFIER_assert(signed_mul(3) == -6);
  return 0;
}
