#include "smack.h"
#include <fenv.h>

// @expect verified

int main(void) {
  int rm = fegetround();
  assume(rm < 1 || rm > 5);

  assert(rm < 0);

  return 0;
}
