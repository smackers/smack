// simple.c
#include "../../include/smack/smack.h"

int incr(int x) {
  return x + 1;
}

int main(void) {
  int a;

  a = 1;
  a = incr(a);
  assert(a == 2);
  return 0;
}

