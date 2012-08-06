#include <stdio.h>
#include <stdlib.h>
#include "smack.h"

int main(void) {
  int a;

  a = 1;
  a = -1;
  __SMACK_assert(a != -1);
  return a;
}

