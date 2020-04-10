#include "smack.h"
#include <stdio.h>

// @expect verified

int main(void) {
  printf("Hello World\n");
  printf("Hello World %d\n", 10);
  printf("Hello World %d %d\n", 10, 20);
  printf("Hello World %d %d %d\n", 10, 20, 30);
  printf("Hello World %d %d %d\n", 10, 20, 30);
  printf("Hello World %d %d %d %d\n", 10, 20, 30, 40);
}
