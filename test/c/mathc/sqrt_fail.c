#include "smack.h"
#include <assert.h>
#include <math.h>

// @expect error
// @flag --integer-encoding=bit-vector

int main(void) {
  double NaN = 0.0 / 0.0;
  double Inf = 1.0 / 0.0;
  double negInf = -1.0 / 0.0;

  double a = 4.0;
  double b = 4.0 / 9.0;
  double c = -1.0;
  assert(fabs(2.0 - sqrt(a)) < 1e-8);
  assert(fabs(2.0 / 3.0 - sqrt(b)) < 1e-8);
  assert(!__isnan(sqrt(c)));

  assert(sqrt(0.0) == 0.0);
  assert(sqrt(-0.0) == -0.0);
  int isNeg = __signbit(sqrt(-0.0));
  assert(isNeg);

  assert(sqrt(Inf) == Inf);
  assert(__isnan(sqrt(negInf)));

  assert(__isnan(sqrt(NaN)));

  return 0;
}
