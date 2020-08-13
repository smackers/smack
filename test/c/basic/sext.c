#include "smack.h"
#include <limits.h>

// @expect verified
// @flag --wrapped-integer-encoding

int main(void) {
  int xs = INT_MAX;
  long xl = xs;
  assert(xl == INT_MAX);
  xs = -1;
  xl = xs;
  assert(xl == -1);
  return 0;
}
