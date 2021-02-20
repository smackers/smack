#include "smack.h"
#include <stdlib.h>

// @expect verified

int x;
int main(void) {
  int *a = &x;
  int c = a[0];
  return c;
}
