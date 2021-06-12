#include "smack.h"
#include <assert.h>

// @expect verified

int main(void) {
  int x = 0, y = 4;

  while (1) {
    x = x + y;
    y = y + 4;
    assert(x != 30);
  }
  return 0;
}
