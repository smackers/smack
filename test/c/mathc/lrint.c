#include "smack.h"
#include <assert.h>
#include <fenv.h>
#include <math.h>

// @expect verified
// @flag --integer-encoding=bit-vector

int main(void) {
  double NaN = 0.0 / 0.0;
  double Inf = 1.0 / 0.0;
  double negInf = -1.0 / 0.0;

  double a = -2.5;
  double b = -2.4999999999;
  double c = -2.5000000001;
  double d = 8.3;

  fesetround(FE_TONEAREST);
  assert(lrint(a) == -2);
  assert(lrint(b) == -2);
  assert(lrint(c) == -3);
  assert(lrint(d) == 8);

  fesetround(FE_UPWARD);
  assert(lrint(a) == -2);
  assert(lrint(b) == -2);
  assert(lrint(c) == -2);
  assert(lrint(d) == 9);

  fesetround(FE_DOWNWARD);
  assert(lrint(a) == -3);
  assert(lrint(b) == -3);
  assert(lrint(c) == -3);
  assert(lrint(d) == 8);

  fesetround(FE_TOWARDZERO);
  assert(lrint(a) == -2);
  assert(lrint(b) == -2);
  assert(lrint(c) == -2);
  assert(lrint(d) == 8);

  assert(lrint(0.0) == 0);
  assert(lrint(-0.0) == 0);

  return 0;
}
