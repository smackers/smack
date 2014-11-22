#include <stdio.h>
#include <stdlib.h>
#include "smack.h"

short incr(short x) {
  return ++x;
}

int main(void) {
  short a;

  a = -1;
  a = incr(a);
  assert(a == 0);
  return a;
}

