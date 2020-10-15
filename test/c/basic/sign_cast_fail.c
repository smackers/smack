#include "smack.h"
#include <assert.h>
#include <limits.h>

// @expect error

int main(void) {
  unsigned x = __VERIFIER_nondet_unsigned();

  // -n's two's complement is UNINT_MAX - (n - 1)
  assume(x < UINT_MAX - 1);
  assert(x < ((unsigned)-3));
  return 0;
}
