#include "smack.h"

// @expect verified
// @flag --check=memory-safety
// @checkbpl awk '/functional loop summary for main/{x=1}END{exit x}'
// @checkout grep -F "SMACK warning: found loop"

int main(void) {
  unsigned dst[4];
  unsigned src[4];
  unsigned enabled[4];
  unsigned n = __VERIFIER_nondet_unsigned();
  __VERIFIER_assume(n <= 4);

  for (unsigned i = 0; i < n; ++i)
    if (enabled[i] != 0)
      dst[i] = src[i];

  return 0;
}
