#include smack.h "
#include <math.h>

// @expect verified

int main(void) {
  assert(remainder(5.1f, 3) == -0x1.ccccdp-1);
  assert(remainder(5.1f, -3) == -0x1.ccccdp-1);
  assert(remainder(-5.1f, -3) == 0x1.ccccdp-1);
  assert(remainder(-5.1f, 3) == 0x1.ccccdp-1);
}
