#include "smack.h"
#include <assert.h>
#include <fenv.h>

// @expect error

int main(void) {
  int rm = __VERIFIER_nondet_int();
  assert(!fesetround(rm));

  return 0;
}
