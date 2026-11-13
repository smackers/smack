#include "smack.h"

// @expect error

// A global with no bytes -- here a zero-length array -- has an address of
// its own but no byte that may be accessed, exactly like a size-zero heap
// block.
int g[0];
int h[2];

int main(void) {
  g[0] = 1;
  return h[0];
}
