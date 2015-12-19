#include<stdio.h>
#include<stdlib.h>
#include<smack.h>

// @flag --memory-safety
// @expect error

int main() {
  int* a;
  int b = a[0];
  printf("%d\n", b);
  return 0;
}
