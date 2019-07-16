#include "smack.h"
#include <string.h>

// @flag --memory-safety
// @expect error

int main(void) {
  const char *sentence = "long";
  char container[2];
  strcpy(container, sentence); // buffer overflow!
  return 0;
}
