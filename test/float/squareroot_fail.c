#include <stdio.h>
#include <stdlib.h>
#include "smack.h"

// @expect error

int main() {
  double a;
  double b;
  
  a = sqrt(4.01);
  b = 2.0;
  
  assert(a == b);
}