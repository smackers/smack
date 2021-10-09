#include "smack.h"
#include <assert.h>
#include <math.h>

// @expect verified
// @flag --integer-encoding=bit-vector

int main(void) {
  float NaN = 0.0f / 0.0f;
  float Inf = 1.0f / 0.0f;
  float negInf = -1.0f / 0.0f;

  float a = -1.5f;
  float b = -1.49999999999999999f;
  float c = 3.5f;
  float d = 2.0f;

  assert(lroundf(a) == -2);
  assert(lroundf(b) == -1);
  assert(lroundf(c) == 4);
  assert(lroundf(d) == 2);

  assert(lroundf(0.0f) == 0);
  assert(lroundf(-0.0f) == 0);
  int isNeg = __signbitf(lroundf(-0.0f));
  assert(isNeg);

  return 0;
}
