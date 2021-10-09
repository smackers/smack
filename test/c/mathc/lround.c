#include "smack.h"
#include <assert.h>
#include <math.h>

// @expect verified
// @flag --integer-encoding=bit-vector

int main(void) {
  double NaN = 0.0 / 0.0;
  double Inf = 1.0 / 0.0;
  double negInf = -1.0 / 0.0;

  double a = -1.5;
  double b = -1.49999999999999999;
  double c = 3.5;
  double d = 2.0;

  assert(lround(a) == -2);
  assert(lround(b) == -1);
  assert(lround(c) == 4);
  assert(lround(d) == 2);

  assert(lround(0.0) == 0);
  assert(lround(-0.0) == 0);
  int isNeg = __signbit(lround(-0.0));
  assert(isNeg);

  return 0;
}
