#include "smack.h"
#include <stddef.h>
#include <stdint.h>

// @flag --sign-analysis
// @expect error

// A negative literal as the MINUEND is not an offset: SIZE_MAX - b is the
// unsigned quantity 2^64 - 1 - b (the aws-c-common overflow-check idiom), and
// -1 - x under a signed consumer is the signed quantity. The literal follows
// the window of the result, not the offset rule that governs x + (-k).
int main(void) {
  size_t b = __VERIFIER_nondet_ulong();
  __VERIFIER_assume(b < 100);
  __VERIFIER_assert(SIZE_MAX - b < SIZE_MAX - 100); // unsigned minuend
  int x = __VERIFIER_nondet_int();
  __VERIFIER_assume(x > 0);
  __VERIFIER_assert(-1 - x < 0); // signed minuend
  return 0;
}
