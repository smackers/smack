#include "smack.h"
#include <assert.h>
#include <limits.h>

// @expect verified
// @flag --integer-encoding=wrapped-integer

int main(void) {
  unsigned x = __VERIFIER_nondet_unsigned();
  unsigned uint32_max = 0xffffffff;

  assume(x > uint32_max - 1);
  assert(x > ((unsigned)-3));
  return 0;
}
