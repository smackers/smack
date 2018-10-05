#include "smack.h"
#include <fenv.h>

// @expect error

int main(void) {
  int rm = __VERIFIER_nondet_int();
  assert(!fesetround(rm));

  return 0;
}
