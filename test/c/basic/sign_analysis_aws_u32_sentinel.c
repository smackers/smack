#include "smack.h"
#include <stdint.h>
// @flag --sign-analysis
// @expect verified
static uint32_t find(uint32_t key) {
  if (key == 7u)
    return 3u;
  return 4294967295U; /* "not found" */
}
int main(void) {
  uint32_t k = __VERIFIER_nondet_uint();
  uint32_t r = find(k);
  uint32_t half = r / 2u; /* unsigned consumer (udiv) */
  if (k != 7u)
    __VERIFIER_assert(r == 4294967295U);
  else
    __VERIFIER_assert(!(r == 4294967295U) && half == 1u);
  return 0;
}
