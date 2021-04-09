#include "smack.h"
#include <stdlib.h>

// @flag --checked-functions main
// @expect verified

void fun() { __VERIFIER_assert(__VERIFIER_nondet_int()); }

int main() { fun(); }
