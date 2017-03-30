#include <stdio.h>
#include <stdlib.h>
#include "smack.h"

// @expect error

typedef struct {
  int a;
  int b;
} S1;

typedef struct {
  int x;
} S2;

int main(void) {
  S1 s1;
  S2* p2 = (S2*)(&s1);

  s1.a = 3;
  p2->x = 4;

  assert(s1.a == 3);
  return 0;
}

