#include "smack.h"
#include <assert.h>
#include <fenv.h>
#include <math.h>

// @expect error
// @flag --integer-encoding=bit-vector

int main(void) {
  double NaN = 0.0 / 0.0;
  double Inf = 1.0 / 0.0;
  double negInf = -1.0 / 0.0;

  double a = -3.5;
  double b = -3.4999999999;
  double c = -3.5000000001;
  double d = 7.3;

  fesetround(FE_TONEAREST);
  assert(nearbyint(a) == -3.0);
  assert(nearbyint(b) == -3.0);
  assert(nearbyint(c) == -4.0);
  assert(nearbyint(d) == 7.0);

  fesetround(FE_UPWARD);
  assert(nearbyint(a) == -3.0);
  assert(nearbyint(b) == -3.0);
  assert(nearbyint(c) == -3.0);
  assert(nearbyint(d) == 8.0);

  fesetround(FE_DOWNWARD);
  assert(nearbyint(a) == -4.0);
  assert(nearbyint(b) == -4.0);
  assert(nearbyint(c) == -4.0);
  assert(nearbyint(d) == 7.0);

  fesetround(FE_TOWARDZERO);
  assert(nearbyint(a) == -3.0);
  assert(nearbyint(b) == -3.0);
  assert(nearbyint(c) == -3.0);
  assert(nearbyint(d) == 7.0);

  assert(nearbyint(0.0) == 0.0);
  assert(nearbyint(-0.0) == -0.0);
  int isNeg = __signbit(nearbyint(-0.0));
  assert(isNeg);

  assert(nearbyint(Inf) == Inf);
  assert(nearbyint(negInf) == negInf);

  assert(__isnan(nearbyint(NaN)));

  return 0;
}
