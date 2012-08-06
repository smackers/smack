#include <stdio.h>
#include <stdlib.h>
#include "smack.h"

struct int_ops {
  int data;
  int (*incr)(int);
  int (*decr)(int);
};

struct ops {
  int a;
  int b;
  struct int_ops *iops;
};

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

struct int_ops my_int_ops = {
  .data = 10,
  .incr = incr,
  .decr = decr
};

struct ops my_ops = {
  .a = 4,
  .b = 5,
  &my_int_ops
};

int main() {
  int (*fp)(int);
  int x;

  x = 0;
  fp = my_ops.iops->incr;
  x = fp(x);

  __SMACK_assert(x == 1);

  return 0;
}
