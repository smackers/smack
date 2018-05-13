#include "smack.h"
#include <math.h>

// @expect verified

int main(void) {
  double NaN = 0.0 / 0.0;
  double Inf = 1.0 / 0.0;
  double negInf = -1.0 / 0.0;

  double val = __VERIFIER_nondet_double();

  if (!__isnan(val) && !__isinf(val) && !__iszero(val)) {
    if (val > 1) {
      //assert(sqrt(val) <= val);
    } else if (val > 0) {
      //assert(sqrt(val) >= val);
    } else {
      //assert(__isnan(sqrt(val)));
    }
  }

  assert(sqrt(0.0) == 0.0);
  assert(sqrt(-0.0) == -0.0);
  int isNeg = __signbit(sqrt(-0.0));
  assert(isNeg);

  assert(sqrt(Inf) == Inf);
  assert(__isnan(sqrt(negInf)));

  assert(__isnan(sqrt(NaN)));

  return 0;
}
