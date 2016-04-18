#include<stdio.h>
#include<stdlib.h>
#include<smack.h>

// @flag --memory-safety
// @expect error

void freeMemory (int* pointer) {
  free(pointer);
}

int main() {
  int* a = malloc(10*sizeof(int));
  freeMemory(a);
  int b = a[9];
  printf("%d\n", b);
  return 0;
}
