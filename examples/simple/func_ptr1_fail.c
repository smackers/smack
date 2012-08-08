#include <stdio.h>
#include <stdlib.h>
#include "smack.h"

int incr(int x) {
  return ++x;
}

int decr(int x) {
  return --x;
}

int main() {
  int (*fp)(int);
  int x;

  x = 0;
  if (__SMACK_nondet()) {
    fp = incr;
  } else {
    fp = decr;
  }  
  x = fp(x);

  __SMACK_assert(x == 1);

  return 0;
}

