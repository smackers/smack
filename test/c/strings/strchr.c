#include "smack.h"
#include <assert.h>
#include <string.h>

// @expect verified

int main(void) {
  char *sentence = "a..b";
  char *withoutFirstWord = strchr(sentence, '.');

  assert(strcmp(withoutFirstWord, "..b") == 0);
  return 0;
}
