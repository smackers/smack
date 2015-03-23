#include "smack.h"

// @expect error
// @flag --unroll=1

void __SMACK_INIT(test) {
  // A call to this function should be injected in main, and
  //  cause verification to fail
  assert(0);
}

void main() {
  int a = 1;
  assert(a==1);
}
