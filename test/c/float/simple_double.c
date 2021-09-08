#include "smack.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

// @expect verified

int main(void) {
  double a;

  a = 3.0;
  a = 1.5;
  assert(a == 1.5);
  return 0;
}
