#include "smack.h"
#include <assert.h>
#include <math.h>

// @expect verified
// @flag --integer-encoding=bit-vector

int main(void) {
  float NaN = 0.0f / 0.0f;
  float Inf = 1.0f / 0.0f;
  float negInf = -1.0f / 0.0f;

  float val = __VERIFIER_nondet_float();

  if (!__isnanf(val) && !__isinff(val) && !__iszerof(val)) {
    if (val > 0) {
      assert(fabsf(val) == val);
    } else {
      assert(fabsf(val) == -val);
    }
  }

  assert(fabsf(0.0f) == 0.0f);
  assert(fabsf(-0.0f) == 0.0f);
  int isNeg = __signbitf(fabsf(-0.0f));
  assert(!isNeg);

  assert(fabsf(Inf) == Inf);
  assert(fabsf(negInf) == Inf);

  assert(__isnanf(fabsf(NaN)));

  return 0;
}
