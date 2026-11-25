#include "smack.h"
#include <assert.h>

// @expect verified
// The callee writes only to an object the assertion never reads.

void store(int *p) { *p = 7; }

int main(void) {
  int watched = 1;
  int other = 0;
  store(&other);
  assert(watched == 1);
  return 0;
}
