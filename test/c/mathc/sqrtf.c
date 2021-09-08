#include "smack.h"
#include <assert.h>
#include <math.h>

// @expect verified
// @flag --integer-encoding=bit-vector

int main(void) {
  float NaN = 0.0f / 0.0f;
  float Inf = 1.0f / 0.0f;
  float negInf = -1.0f / 0.0f;

  float a = 4.0f;
  float b = 4.0f / 9.0f;
  float c = -1.0f;
  assert(fabsf(2.0f - sqrtf(a)) < 1e-8);
  assert(fabsf(2.0f / 3.0f - sqrtf(b)) < 1e-8);
  assert(__isnanf(sqrtf(c)));

  assert(sqrtf(0.0f) == 0.0f);
  assert(sqrtf(-0.0f) == -0.0f);
  int isNeg = __signbitf(sqrtf(-0.0f));
  assert(isNeg);

  assert(sqrtf(Inf) == Inf);
  assert(__isnanf(sqrtf(negInf)));

  assert(__isnanf(sqrtf(NaN)));

  return 0;
}
