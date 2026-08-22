#include "smack.h"
#include <assert.h>

// @expect error
// A pointer cast keeps both accesses on one sea-DSA node, so the store must be
// retained even though the types differ.

int main(void) {
  int x = 0;
  char *c = (char *)&x;
  *c = 1;
  assert(x == 0);
  return 0;
}
