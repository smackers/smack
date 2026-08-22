#include "smack.h"
#include <assert.h>

// @expect error
// The callee writes through a pointer the assertion reads: the call must be
// retained on the strength of its region effect alone, not its result.

void store(int *p) { *p = 7; }

int main(void) {
  int x = 0;
  store(&x);
  assert(x != 7);
  return 0;
}
