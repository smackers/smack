#include <string.h>
#include "smack.h"

// @expect verified

int main(void) {
  char *shorty = "go";
  char *otherShorty = "go";
  int comparison = strncmp(shorty, otherShorty, 5);

  assert(comparison == 0); 
  return 0;
}
