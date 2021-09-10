#include "smack.h"
#include <assert.h>
#include <limits.h>

// @expect error
// @flag --integer-encoding=wrapped-integer

int main(void) {
  unsigned xs = UINT_MAX;
  unsigned long xl = xs;
  assert(xl == UINT_MAX);
  long yl = xs;
  assert(yl != xl);
  return 0;
}
