//
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "incr.h"

int incr(int x) {
  int y = __VERIFIER_nondet_int();
  assume(y > 0 && y < 10000); // prevents overflow when bit-precise
  return x + y;
}
