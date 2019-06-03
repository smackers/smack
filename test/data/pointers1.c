#include "smack.h"
#include <stdio.h>
#include <stdlib.h>

// @expect verified

typedef struct {
  int a;
  int b;
} point;

void incr(point *p) {
  p->a++;
  p->b++;
}

int main() {
  point *p = (point *)malloc(sizeof(int));

  p->a = p->b = 0;

  incr(p);

  assert(p->a == 1);
  assert(p->b == 1);

  return 0;
}
