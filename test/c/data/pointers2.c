#include "smack.h"
#include <stdio.h>
#include <stdlib.h>

// @expect verified

typedef struct {
  int a;
  int b;
} point;

point p;

void incr(point *p) {
  p->a += 2;
  p->b += 2;
}

void decr(point *p) {
  p->a--;
  p->b--;
}

int main() {
  p.a = p.b = 0;

  incr(&p);
  decr(&p);

  assert(p.a == 1);
  assert(p.b == 1);

  return 0;
}
