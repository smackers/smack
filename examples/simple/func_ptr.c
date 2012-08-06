#include <stdio.h>
#include <stdlib.h>
#include "smack.h"

void __SMACK_anno_incr(int x) {
  INLINE(__SMACK_inline());
}
int incr(int x) {
  return ++x;
}

void __SMACK_anno_decr(int x) {
  INLINE(__SMACK_inline());
}
int decr(int x) {
  return --x;
}

int main() {
  int (*fp)(int);
  int x;

  x = 0;
  fp = incr;
  x = fp(x);

  __SMACK_assert(x == 1);

  return 0;
}
