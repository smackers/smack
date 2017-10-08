#include <string.h>
#include "smack.h"

// @flag --memory-safety
// @expect error

int main(void) {
  const char *sentence = "long";
  char container[2];
  strcpy(container,sentence); // buffer overflow!
  return 0;
}

