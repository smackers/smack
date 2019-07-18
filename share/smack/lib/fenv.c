//
// This file is distributed under the MIT License. See LICENSE for details.
//
#include <fenv.h>
#include <smack.h>

int fegetround(void) {
  const int CONST_FE_TONEAREST = FE_TONEAREST;
  const int CONST_FE_DOWNWARD = FE_DOWNWARD;
  const int CONST_FE_UPWARD = FE_UPWARD;
  const int CONST_FE_TOWARDZERO = FE_TOWARDZERO;
  int ret = __VERIFIER_nondet_int();
  __VERIFIER_assume(ret < 0);
  __SMACK_code("if ($rmode == RNE) {@ := @;}", ret, CONST_FE_TONEAREST);
  __SMACK_code("if ($rmode == RTN) {@ := @;}", ret, CONST_FE_DOWNWARD);
  __SMACK_code("if ($rmode == RTP) {@ := @;}", ret, CONST_FE_UPWARD);
  __SMACK_code("if ($rmode == RTZ) {@ := @;}", ret, CONST_FE_TOWARDZERO);
  return ret;
}

int fesetround(int rm) {
  switch (rm) {
  case FE_TONEAREST:
    __SMACK_code("$rmode := RNE;");
    break;
  case FE_DOWNWARD:
    __SMACK_code("$rmode := RTN;");
    break;
  case FE_UPWARD:
    __SMACK_code("$rmode := RTP;");
    break;
  case FE_TOWARDZERO:
    __SMACK_code("$rmode := RTZ;");
    break;
  default:
    return 1;
  }
  return 0;
}
