#include <stdlib.h>
#include "smack.h"

// @expect error

typedef struct _strct {
  int a[10];
  int b[10];
  char c;
} strct;

int main(void) {
  strct* s = malloc(sizeof(strct));
  int x = s->a[22];
  free(s);
  return x;
}

