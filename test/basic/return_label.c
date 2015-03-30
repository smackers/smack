#include "smack.h"

// @flag --unroll=2
// @expect verified

int main() {
  int x = __VERIFIER_nondet_int();

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

