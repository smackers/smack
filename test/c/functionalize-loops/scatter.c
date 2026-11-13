#include "smack.h"

// @expect verified
// @checkbpl awk '/functional loop summary/{x=1}END{exit x}'

int main(void) {
  unsigned a[4096];
  unsigned index[4096];
  unsigned n = __VERIFIER_nondet_unsigned();
  __VERIFIER_assume(n <= 4096);

  for (unsigned i = 0; i < n; ++i)
    a[index[i]] = i;

  return 0;
}
