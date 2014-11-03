#include <stdio.h>
#include <stdlib.h>
#include "smack.h"

int main(void) {
  int a;
  int b;

  a = 1;
  b = 2;
  a = -1;
  assert(b == 3 || a == -1 || b == 0);
  return a;
}

