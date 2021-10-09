#include "smack.h"
#include <assert.h>
#include <math.h>

// @expect verified

int main(void) {
  long double NaN = 0.0l / 0.0l;
  long double Inf = 1.0l / 0.0l;
  long double negInf = -1.0l / 0.0l;

  long double a = -1.5l;
  long double b = -1.49999999999999999l;
  long double c = 3.5l;
  long double d = 2.0l;

  assert(lroundl(a) == -2);
  assert(lroundl(b) == -1);
  assert(lroundl(c) == 4);
  assert(lroundl(d) == 2);

  assert(lroundl(0.0l) == 0);
  assert(lroundl(-0.0l) == 0);
  int isNeg = __signbitl(lroundl(-0.0l));
  assert(isNeg);

  return 0;
}
