#include "smack.h"
#include <assert.h>
#include <stdlib.h>

// @flag --checked-functions main fun
// @expect error

void fun() { assert(__VERIFIER_nondet_int()); }

int main() { fun(); }
