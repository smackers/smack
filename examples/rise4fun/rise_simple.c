#include "smack.h"
#include <assert.h>

int main(void) {
  int x, y, z;

  x = 10;
  y = 20;
  z = x + y;
  assert(z == 30);
  return 0;
}
