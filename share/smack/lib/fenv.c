// This file is distributed under the MIT License. See LICENSE for details.
//
#include <fenv.h>
#include <smack.h>

int fegetround(void) {
  int ret = __VERIFIER_nondet_int();
  assume(ret < 0);
  __SMACK_code("if ($rmode == RNE) {@ := 0;}", ret);
  __SMACK_code("if ($rmode == RTN) {@ := 1024;}", ret);
  __SMACK_code("if ($rmode == RTP) {@ := 2048;}", ret);
  __SMACK_code("if ($rmode == RTZ) {@ := 3072;}", ret);
  return ret;
}

int fesetround(int rm) {
  switch (rm) {
  case FE_TONEAREST: __SMACK_code("$rmode := RNE;"); break;
  case FE_DOWNWARD: __SMACK_code("$rmode := RTN;"); break;
  case FE_UPWARD: __SMACK_code("$rmode := RTP;"); break;
  case FE_TOWARDZERO: __SMACK_code("$rmode := RTZ;"); break;
  default: return 1;
  }
  return 0;
}

