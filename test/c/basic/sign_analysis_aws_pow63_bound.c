#include "smack.h"
#include <stddef.h>
#include <stdint.h>
// @flag --sign-analysis
// @expect verified
int main(void) {
  size_t n = __VERIFIER_nondet_ulong();
  __VERIFIER_assume(n <= 9223372036854775808U); /* 2^63 */
  size_t twice = n * 2;                         /* fits in size_t */
  __VERIFIER_assert(twice >= n);
  __VERIFIER_assert(n < 18446744073709551615UL);
  return 0;
}
