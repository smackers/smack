#include <string.h>
#include "smack.h"

// @flag --unroll=5
// @expect verified

int main(void) {
  char *smaller = "AAAA";
  char *bigger = "aaaa";

  int comparison = strcmp(smaller,bigger);

  assert(comparison < 0);
  return 0;
}
