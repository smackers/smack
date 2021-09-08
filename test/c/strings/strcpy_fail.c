#include "smack.h"
#include <assert.h>
#include <string.h>

// @expect error

int main(void) {
  const char *word = "made";
  char container[5];

  strcpy(container, word);
  assert(strcmp(container, "made") != 0);
  return 0;
}
