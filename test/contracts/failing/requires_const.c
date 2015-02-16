#include <stdio.h>
#include <stdlib.h>
#include "smack-defs.h"

// @expect 1 verified, 0 errors?

void p() {
  requires(true);
}
