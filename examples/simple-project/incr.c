//
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "incr.h"

int incr(int x) {
  int y = __SMACK_nondet();
  assume(y > 0);
  return x + y;
}

