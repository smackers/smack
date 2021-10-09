#include "smack.h"
#include <assert.h>
#include <math.h>

// @expect error

int main(void) {
  long double NaN = 0.0l / 0.0l;
  long double Inf = 1.0l / 0.0l;
  long double negInf = -1.0l / 0.0l;

  long double a = 4.0l;
  long double b = 4.0l / 9.0l;
  long double c = -1.0l;
  assert(fabsl(2.0l - sqrtl(a)) < 1e-8);
  assert(fabsl(2.0l / 3.0l - sqrtl(b)) < 1e-8);
  assert(__isnanl(sqrtl(c)));

  assert(sqrtl(0.0l) == 0.0l);
  assert(sqrtl(-0.0l) == -0.0l);
  int isNeg = __signbitl(sqrtl(-0.0l));
  assert(!isNeg);

  assert(sqrtl(Inf) == Inf);
  assert(__isnanl(sqrtl(negInf)));

  assert(__isnanl(sqrtl(NaN)));

  return 0;
}
