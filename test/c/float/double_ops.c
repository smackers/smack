#include "smack.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

// @expect verified

int main(void) {
  double a;
  double b;
  double c;

  a = 1.5;
  b = 2.25;
  c = a + b;
  assert(c == 3.75);

  a = 1.5;
  b = 2.25;
  c = a - b;
  assert(c == -0.75);

  a = 1.5;
  b = 3.0;
  c = a * b;
  assert(c == 4.5);

  a = 3.0;
  b = 1.5;
  c = a / b;
  assert(c == 2.0);
  return 0;
}
