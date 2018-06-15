#include "smack.h"
#include <math.h>

// @expect verified

int main(void)
{
  assert(!__signbit(remainder(0.0, 1.0)));
}
