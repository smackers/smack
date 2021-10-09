#include "smack.h"
#include <assert.h>

// @expect verified
// @flag --llvm-assumes=check
// @flag --integer-encoding=bit-vector

int main(void) {
  unsigned int x = __VERIFIER_nondet_unsigned_int();
  unsigned int y = __VERIFIER_nondet_unsigned_int();
  // This assumption is checked under integer-encoding=bit-vector and is
  // verified.
  __builtin_assume((x ^ y) == (y ^ x));
  assert((x ^ y) == (y ^ x));
  return 0;
}
