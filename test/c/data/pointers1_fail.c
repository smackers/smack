#include "smack.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

// @expect error

typedef struct {
  int a;
  int b;
} point;

void incr(point *p) {
  p->a++;
  p->b++;
  p->a++;
}

int main() {
  point *p = (point *)malloc(sizeof(int));

  p->a = p->b = 0;

  incr(p);

  assert(p->a == 1);
  assert(p->b == 1);

  return 0;
}
