#include "smack.h"
#include <assert.h>

// @expect error
// @flag --llvm-assumes=none

int main(void) {
  unsigned int x = __VERIFIER_nondet_unsigned_int();
  unsigned int y = __VERIFIER_nondet_unsigned_int();
  // This assumption is not used, and since integer-encoding=bit-vector is
  // not enabled, verification will fail.
  __builtin_assume((x ^ y) == (y ^ x));
  assert((x ^ y) == (y ^ x));
  return 0;
}
