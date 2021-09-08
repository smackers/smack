#include "smack.h"
#include <assert.h>

// @expect error
// @flag --integer-encoding=wrapped-integer

int main() {
  unsigned x = 2;
  unsigned y = 3;
  assert(x - y < 1);
  return 0;
}
