#include <stdio.h>
#include <stdlib.h>
#include "smack.h"

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
  point* p = (point*)malloc(sizeof(int));

  p->a = p->b = 0;

  incr(p);

  __SMACK_assert(p->a == 1);
  __SMACK_assert(p->b == 1);

  return 0;
}

