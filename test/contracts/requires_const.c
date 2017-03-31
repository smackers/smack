#include <stdio.h>
#include <stdlib.h>
#include <smack.h>
#include <smack-contracts.h>

// @expect verified

void p() {
  requires(true);
}
