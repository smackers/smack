#include "smack.h"
#include <assert.h>

// @flag --checked-functions should_match.*
// @expect error

int should_match1() { assert(1); }

int should_match12() { assert(0); }

int main() {
  should_match1();
  should_match12();
}
