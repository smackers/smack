#include "smack.h"

// @expect error
// @checkbpl grep -E ":= if.+then.+else.+"

int main(void) {
  int c = 2;
  assert(c != 2 ? 1 : 0);
}
