#include <stdio.h>
#include <stdlib.h>
#include "smack.h"

void __SMACK_anno_incr(int *x) {
  INLINE(__SMACK_inline());
}
void incr(int *x) {
  (*x)++;
}

void __SMACK_anno_decr(int *x) {
  INLINE(__SMACK_inline());
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
