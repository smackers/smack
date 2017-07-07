#include <stdio.h>
#include <stdlib.h>
#include "smack.h"

// @expect error

int main(void) {
  float a;
  float b;
  float c;

  a = 1.5f;
  b = 2.25f;
  c = a * (b / a);
  assert(c == 2.0f);
  
  return 0;
}
