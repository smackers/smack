#include "smack.h"
#include <assert.h>
#include <math.h>

// @expect error
// @flag --integer-encoding=bit-vector

int main(void) {
  float NaN = 0.0f / 0.0f;
  float Inf = 1.0f / 0.0f;
  float negInf = -1.0f / 0.0f;

  float val = __VERIFIER_nondet_float();

  if (!__isnanf(val) && !__isinff(val) && !__iszerof(val)) {
    if (val > 0) {
      assert(truncf(val) <= val);
    } else {
      assert(truncf(val) >= val);
    }
  }

  assert(truncf(0.0f) == 0.0f);
  assert(truncf(-0.0f) == -0.0f);
  int isNeg = __signbitf(truncf(-0.0f));
  assert(isNeg);

  assert(truncf(Inf) == Inf);
  assert(truncf(negInf) == negInf);

  assert(!__isnanf(truncf(NaN)));

  return 0;
}
