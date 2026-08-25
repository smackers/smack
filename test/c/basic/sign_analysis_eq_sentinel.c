// This file is distributed under the MIT License. See LICENSE for details.
// @expect verified
// @flag --sign-analysis
// @flag --unroll=8
// @checkbpl grep -F '$i5 := 18446744073709551615;'
// @checkbpl grep -F '$ne.i64($i4, 18446744073709551615)'

// The SIZE_MAX sentinel returned by find() is consumed by `!=` and by an
// unsigned compare. Both literals that meet r must be spelled in the same
// window: if the returned literal were 2^64-1 and the equality literal -1,
// `r != SIZE_MAX` would be a tautology and the assertion reachable.

#include "smack.h"
#include <stddef.h>
#include <stdint.h>

size_t find(size_t n) {
  size_t i;
  for (i = 0; i < n; i++)
    if (__VERIFIER_nondet_int())
      return i;
  return (size_t)-1;
}

int main(void) {
  size_t n = __VERIFIER_nondet_uint();
  __VERIFIER_assume(n <= 3);
  size_t r = find(n);
  if (r != SIZE_MAX) {
    if (r >= n)
      __VERIFIER_assert(0);
  }
  return 0;
}
