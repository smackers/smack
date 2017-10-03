#include <stdio.h>
#include <stdlib.h>
#include "smack.h"

// @expect error

int main(void) {
  double a;

  a = 3.0;
  a = 1.5;
  assert(a == 1.4);
  return 0;
}
