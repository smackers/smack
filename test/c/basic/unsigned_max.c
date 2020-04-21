#include "smack.h"
#include <limits.h>

// @expect verified
// @flag --wrapped-integer-encoding

int main(void) {
  unsigned x = __VERIFIER_nondet_unsigned();
  unsigned uint32_max = 0xffffffff;

  assume(x > uint32_max - 1);
  assert(x > ((unsigned)-3));
  return 0;
}
