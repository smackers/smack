
#include <string.h>
#include "smack.h"

// @flag --unroll=5
// @expect verified

int main() {
  char *sentence = "a..b";

  char *withoutFirstWord = strchr(sentence,'.');

  assert(strcmp(withoutFirstWord,"..b") == 0); 

  return 0;
}
