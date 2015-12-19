#include<stdio.h>
#include<stdlib.h>
#include<smack.h>

// @flag --memory-safety
// @expect verified

int main() {
  int* a = malloc(10*sizeof(int));
  int b = a[9];
  printf("%d\n", b);
  return 0;
}
