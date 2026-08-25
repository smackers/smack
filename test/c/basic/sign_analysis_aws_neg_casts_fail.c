#include "smack.h"
#include <stddef.h>
#include <stdint.h>
// @flag --sign-analysis
// @expect error
int main(void) {
  size_t all = (size_t)-1; /* 18446744073709551615 */
  int64_t m = INT64_MIN;   /* -9223372036854775808 */
  size_t x = __VERIFIER_nondet_ulong();
  __VERIFIER_assume(x < 100);
  __VERIFIER_assert(all - x >
                    1000); /* unsigned arithmetic on the all-ones value */
  __VERIFIER_assert(m < 0 && m + 1 < 0); /* signed arithmetic on INT64_MIN */
  __VERIFIER_assert((uint64_t)m != 9223372036854775808U);
  return 0;
}
