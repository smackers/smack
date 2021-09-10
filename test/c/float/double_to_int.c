#include "smack.h"
#include <assert.h>

// @flag --integer-encoding=bit-vector
// @expect verified

int main(void) {
  double x = 1.5;
  int y = x;

  assert(y == 1);
}
