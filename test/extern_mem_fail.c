#include <stdlib.h>
#include <smack-defs.h>

void foo(int *);
int* bar();

int main() {
  int *x = malloc(4);
  int *y;

  foo(x);
  y = bar();

  *x = 1;
  *y = 2;

  assert(x != y);
}