#include "smack.h"
#include <assert.h>
#include <math.h>

// @expect error
// @flag --integer-encoding=bit-vector

int main(void) {
  assert(floor(2.7) == 2.0);
  assert(floor(-2.7) == -3.0);
  double c = floor(-0.0);
  assert(c == -0.0);
  assert(sizeof(c) == sizeof(float)    ? __signbitf(c)
         : sizeof(c) == sizeof(double) ? __signbit(c)
                                       : __signbitl(c));
  c = floor(__builtin_inff());
  assert(sizeof((__builtin_inff())) == sizeof(float)
             ? __isinff((__builtin_inff()))
         : sizeof((__builtin_inff())) == sizeof(double)
             ? __isinf((__builtin_inff()))
             : __isinfl((__builtin_inff())));
  assert(sizeof(c) == sizeof(float)    ? __signbitf(c)
         : sizeof(c) == sizeof(double) ? __signbit(c)
                                       : __signbitl(c));
  return 0;
}
