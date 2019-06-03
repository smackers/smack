#include "smack.h"
#include <stdlib.h>

// @expect error

int x;
int main(void) {
  int *a = &x;
  int c = a[1];
  return c;
}
