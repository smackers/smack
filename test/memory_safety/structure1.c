#include<stdio.h>
#include<stdlib.h>
#include<smack.h>

// @flag --memory-safety
// @expect verified

typedef struct _strct {
  float a[10];
  int b[10];
  char c;
} strct;

int main() {
  strct* s = malloc(sizeof(strct));
  float f = s->a[11];
  printf("%f\n", f);
  return 0;
}
