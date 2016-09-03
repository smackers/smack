#include <stdio.h>
#include <stdlib.h>
#include "smack.h"

// @expect error

typedef struct _strct {
  float a[10];
  int b[10];
  char c;
} strct;

int main(void) {
  strct* s = malloc(sizeof(strct));
  float f = s->a[22];
  printf("%f\n", f);
  return 0;
}

