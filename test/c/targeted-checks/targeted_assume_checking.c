#include "smack.h"
#include <stdlib.h>

// @flag --checked-functions main
// @flag --llvm-assumes check
// @flag --check none
// @expect verified

void fun() { __builtin_assume(__VERIFIER_nondet_int() == 0); }

int main() { fun(); }
