#include "smack.h"

// @flag --unroll=2
// @expect verified

int main(void) {
  int x = 1;

  if (__SMACK_nondet()) {
    x++;
  } else {
    x--;
  }

  assert(x == 0 || x == 2);
  return 0;
}

