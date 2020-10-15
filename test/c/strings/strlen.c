#include "smack.h"
#include <assert.h>
#include <stdlib.h>
#include <string.h>

// @expect verified

int main(void) {
  char word[] = "Hi!!";

  assert(strlen(word) == 4);
  return 0;
}
