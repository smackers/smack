#include "smack.h"
#include <assert.h>
#include <math.h>

// @expect verified
// @flag --integer-encoding=bit-vector

int main(void) { assert(!__signbit(remainder(0.0, 1.0))); }
