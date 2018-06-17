#include <fenv.h>
#include <smack.h>

int fegetround()
{
  int ret = __VERIFIER_nondet_int();
  __SMACK_code("if ($rmode == RNE) {@ := 1;}", ret);
  __SMACK_code("if ($rmode == RNA) {@ := 2;}", ret);
  __SMACK_code("if ($rmode == RTP) {@ := 3;}", ret);
  __SMACK_code("if ($rmode == RTN) {@ := 4;}", ret);
  __SMACK_code("if ($rmode == RTZ) {@ := 5;}", ret);
  return ret;
}

int fesetround(int rm) 
{
  switch (rm) {
  case FE_TONEARESTEVEN: __SMACK_code("$rmode := RNE;"); break;
  case FE_TONEARESTAWAY: __SMACK_code("$rmode := RNA;"); break;
  case FE_UPWARD: __SMACK_code("$rmode := RTP;"); break;
  case FE_DOWNWARD: __SMACK_code("$rmode := RTN;"); break;
  case FE_TOWARDZERO: __SMACK_code("$rmode := RTZ;"); break;
  }
  return 0;
}

