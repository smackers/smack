#include <stdio.h>
#include <stdlib.h>
#include "smack.h"

void __SMACK_anno_returnOne() {
  __SMACK_ensures(__SMACK_return == 1);
  INLINE(__SMACK_inline());
}
int returnOne() {
  return 1;
}

int main(void) {
  int a;

  a = -1;
  a = returnOne();
  __SMACK_assert(a == -1);
  return a;
}

