#include "smack.h"

// @expect error

double f16_to_f32(float x) {
  double ret = __VERIFIER_nondet_double();
  __SMACK_code("@ := ftd(RNE, @f);", ret, x);
  return ret;
}

int main(void) {
  assert(f16_to_f32(2.0f) != 2.0);
  return 0;
}

