#include <stdio.h>
#include <stdlib.h>
#include "smack.h"

void __SMACK_anno_incr(int x) {
  __SMACK_requires(x >= 0);
  __SMACK_ensures(__SMACK_return == x + 1);
  INLINE(__SMACK_inline());
}
int incr(int x) {
  return x + 1;
}

int main(void) {
  int a;

  a = 1;
  a = incr(a);
  __SMACK_assert(a == 2);
  return a;
}

