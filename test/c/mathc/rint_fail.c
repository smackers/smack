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

  double a = -4.5;
  double b = -4.4999999999;
  double c = -4.5000000001;
  double d = 5.3;

  fesetround(FE_TONEAREST);
  assert(rint(a) == 4.0);
  assert(rint(b) == -4.0);
  assert(rint(c) == -5.0);
  assert(rint(d) == 5.0);

  fesetround(FE_UPWARD);
  assert(rint(a) == -4.0);
  assert(rint(b) == -4.0);
  assert(rint(c) == -4.0);
  assert(rint(d) == 6.0);

  fesetround(FE_DOWNWARD);
  assert(rint(a) == -5.0);
  assert(rint(b) == -5.0);
  assert(rint(c) == -5.0);
  assert(rint(d) == 5.0);

  fesetround(FE_TOWARDZERO);
  assert(rint(a) == -4.0);
  assert(rint(b) == -4.0);
  assert(rint(c) == -4.0);
  assert(rint(d) == 5.0);

  assert(rint(0.0) == 0.0);
  assert(rint(-0.0) == -0.0);
  int isNeg = __signbit(rint(-0.0));
  assert(isNeg);

  assert(rint(Inf) == Inf);
  assert(rint(negInf) == negInf);

  assert(__isnan(rint(NaN)));

  return 0;
}
