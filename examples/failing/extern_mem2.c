#include <stdlib.h>
#include <smack.h>

void foo(int*);
int* bar();

int main() {
  int *x = malloc(4);
  int *y = malloc(4);
  int *z;

  foo(y);
  z = bar();

  *x = 1;
  *z = 2;

  assert(x != z);
}