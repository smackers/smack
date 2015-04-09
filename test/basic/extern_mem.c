#include <stdlib.h>
#include <smack.h>

// @expect verified

void foo();
int* bar();

int main() {
  int *x = malloc(4);
  int *y;

  foo();
  y = bar();

  *x = 1;
  *y = 2;

  assert(x != y);
}
