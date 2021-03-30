#include "smack.h"
#include <stdlib.h>

// @flag --checked-functions main fun
// @expect error

void fun() { __VERIFIER_assert(__VERIFIER_nondet_int()); }

int main() { fun(); }
