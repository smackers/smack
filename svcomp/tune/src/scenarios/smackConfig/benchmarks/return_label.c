#include "smack.h"

// @flag --unroll=2
// @expect verified

int main() {
  int x = __SMACK_nondet();

  if (x == 0) {
    goto ERROR;
  } else {
    goto out;
  }

  out:
    return 0;
  ERROR:
    return 0;
}

