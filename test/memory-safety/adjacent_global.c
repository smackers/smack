#include <stdlib.h>
#include "smack.h"

// @expect verified

int x;
int main(void) {
  int* a = &x;
  int c = a[0];
  return c;
}

