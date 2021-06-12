#include "smack.h"
#include <assert.h>

// @expect verified
// @flag --llvm-assumes=use

int main(void) {
  unsigned int x = __VERIFIER_nondet_unsigned_int();
  // This assumption is used for verification, even though the assumption
  // is false, the assertion will pass.
  __builtin_assume((x ^ x) == 1);
  assert((x ^ x) == 1);
  return 0;
}
