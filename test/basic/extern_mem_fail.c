#include <smack.h>
#include <stdlib.h>

// @expect error

void foo(int *);
int *bar();

int main() {
  int *x = malloc(4);
  int *y;

  foo(x);
  y = bar();

  *x = 1;
  *y = 2;

  assert(x != y);
}
