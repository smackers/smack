#include "smack.h"
#include <assert.h>

// @flag --integer-encoding=bit-vector
// @expect error

int main(void) {
  double x = 1.5;
  int y = x;

  assert(y == 2);
}
