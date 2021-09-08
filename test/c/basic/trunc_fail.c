#include "smack.h"
#include <assert.h>
#include <limits.h>

// @expect error
// @flag --integer-encoding=wrapped-integer

int main(void) {
  unsigned long xl = ULONG_MAX;
  unsigned xs = xl;
  assert(xs == UINT_MAX);
  long yl = LONG_MAX;
  int ys = yl;
  assert(ys == -1);
  xs = yl;
  ys = xl;
  assert(xs != ys);
  return 0;
}
