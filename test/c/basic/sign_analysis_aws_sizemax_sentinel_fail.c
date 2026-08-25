#include "smack.h"
#include <stddef.h>
#include <stdint.h>
// @flag --sign-analysis
// @expect error
static size_t add_checked(size_t a, size_t b) {
  if (a > SIZE_MAX - b)
    return SIZE_MAX; /* sentinel: 18446744073709551615UL */
  return a + b;
}
int main(void) {
  size_t a = __VERIFIER_nondet_ulong(), b = __VERIFIER_nondet_ulong();
  size_t r = add_checked(a, b);
  size_t q = r / 2; /* unsigned consumer of r */
  if (r == SIZE_MAX)
    __VERIFIER_assert(a > SIZE_MAX - b); /* misses the exact-fit case */
  else
    __VERIFIER_assert(r == a + b);
  return (int)q;
}
