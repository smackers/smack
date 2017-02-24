
#include <strings.h>
#include "smack.h"

// @expect verified

int main() {
  const char *sentence = "A longer string that will overflow";
  char container[10];
  
  strcpy(container,sentence); // buffer overflow!
  assert(strlen(container) == 34);
  assert(strcmp(container,sentence) == 0);
  return 0;
}

