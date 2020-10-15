#include "smack.h"
#include <assert.h>
#include <string.h>

// @expect verified

int main(void) {
  char *smaller = "AAAA";
  char *bigger = "aaaa";
  int comparison = strcmp(smaller, bigger);

  assert(comparison < 0);
  return 0;
}
