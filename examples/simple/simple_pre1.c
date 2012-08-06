#include <stdio.h>
#include <stdlib.h>
#include "smack.h"

void __SMACK_anno_incr(int x) {
  __SMACK_ensures(__SMACK_return == x);
  INLINE(__SMACK_inline());
}
int incr(int x) {
  return x;
}

int main(void) {
  int a;

  a = -1;
  a = incr(a);
  __SMACK_assert(a == -1);
  return a;
}

