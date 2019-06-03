#include "smack.h"
#include <stdio.h>
#include <stdlib.h>

// @expect error

typedef struct { int x; } S1;

typedef struct {
  int a;
  int b;
} S2;

int main(void) {
  S2 *s2 = (S2 *)malloc(sizeof(S2));
  S1 *s1 = (S1 *)s2;

  s2->a = 3;
  s2->b = 5;
  s1->x = 4;

  assert(s2->a == 3);
  return 0;
}
