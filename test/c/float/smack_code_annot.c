#include "smack.h"
#include <assert.h>

// @expect verified

double f32_to_f64(float x) {
  double ret = __VERIFIER_nondet_double();
  __SMACK_code("@ := $fpext.bvfloat.bvdouble(RNE, @f);", ret, x);
  return ret;
}

int main(void) {
  assert(f32_to_f64(2.0f) == 2.0);
  return 0;
}
