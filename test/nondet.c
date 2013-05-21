#include "smack.h"

int main(void) {
  int x = 1;

  if (__SMACK_nondet()) {
    x++;
  } else {
    x--;
  }

  __SMACK_assert(x == 0 || x == 2);
  return 0;
}

