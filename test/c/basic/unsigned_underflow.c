#include "smack.h"
#include <assert.h>

// @expect verified
// @flag --integer-encoding=wrapped-integer

int main() {
  unsigned x = 2;
  unsigned y = 3;
  assert(x - y > 0);
  return 0;
}
