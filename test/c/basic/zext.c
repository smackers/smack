#include "smack.h"
#include <limits.h>

// @expect verified
// @flag --wrapped-integer-encoding

int main(void) {
  unsigned xs = UINT_MAX;
  unsigned long xl = xs;
  assert(xl == UINT_MAX);
  long yl = xs;
  assert(yl == xl);
  return 0;
}
