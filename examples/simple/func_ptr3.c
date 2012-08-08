#include <stdio.h>
#include <stdlib.h>
#include "smack.h"

void incr(int *x) {
  (*x)++;
}

void decr(int *x) {
  (*x)--;
}

int main() {
  void (*fp)(int*);
  int *x = (int*)malloc(sizeof(int));

  *x = 0;
  if (__SMACK_nondet()) {
    fp = incr;
  } else {
    fp = decr;
  }
  fp(x);

  __SMACK_assert(*x == 1 || *x == -1);

  return 0;
}

