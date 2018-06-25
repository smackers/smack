#include "smack.h"
#include <fenv.h>

// @expect error

int main(void) {
  int rm = __VERIFIER_nondet_int();
  assume(rm < 1 || rm >= 5);

  assert(fesetround(rm));

  return 0;
}
