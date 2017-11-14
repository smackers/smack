#include "smack.h"

// @expect verified
// @checkbpl grep -P ":= if.+then.+else.+"

int main(void) {
  int c = 2;
  assert(c == 2 ? 1 : 0);
}
