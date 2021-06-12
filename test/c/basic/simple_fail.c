#include "smack.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

// @expect error

int main(void) {
  int a;

  a = 1;
  a = -1;
  assert(a != -1);
  return a;
}
