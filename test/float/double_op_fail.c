#include <stdio.h>
#include <stdlib.h>
#include "smack.h"

// @expect error

int main(void) {
  double a;
  double b;
  double c;

  a = 1.99;
  b = 50.0;
  c = (a * b) / b;
  assert(c == 2.0);
  
  return 0;
}
