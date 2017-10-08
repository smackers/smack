#include <string.h>
#include "smack.h"

// @expect verified

int main(void) {
  char *sentence = "a..b";
  char *withoutFirstWord = strchr(sentence,'.');

  assert(strcmp(withoutFirstWord,"..b") == 0); 
  return 0;
}
