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

int incr(int x) {
  return ++x;
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

  assert(x == 1);

  return 0;
}

