#include "smack.h"
#include <assert.h>

// @expect verified
// @flag --llvm-assumes=use

int main(void) {
  unsigned int x = __VERIFIER_nondet_unsigned_int();
  unsigned int y = __VERIFIER_nondet_unsigned_int();
  // This assumption is used for verification, even though
  // integer-encoding=bit-vector is not enabled, the assertion will pass.
  __builtin_assume((x ^ y) == (y ^ x));
  assert((x ^ y) == (y ^ x));
  return 0;
}
