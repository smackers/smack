#include "smack.h"
#include <assert.h>
#include <stdlib.h>

// @flag --checked-functions main
// @expect verified

void fun() { assert(__VERIFIER_nondet_int()); }

int main() { fun(); }
