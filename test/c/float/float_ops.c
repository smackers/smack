#include "smack.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

// @expect verified

int main(void) {
  float a;
  float b;
  float c;

  a = 1.5f;
  b = 2.25f;
  c = a + b;
  assert(c == 3.75f);

  a = 1.5f;
  b = 2.25f;
  c = a - b;
  assert(c == -0.75f);

  a = 1.5f;
  b = 3.0f;
  c = a * b;
  assert(c == 4.5f);

  a = 3.0f;
  b = 1.5f;
  c = a / b;
  assert(c == 2.0f);
  return 0;
}
