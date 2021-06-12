#include "smack.h"
#include <assert.h>
#include <string.h>

// @expect verified

int main(void) {
  char *string = "a-b";
  char *delim = "-";
  char *firstTok = strtok(string, delim);
  char *nextTok = strtok(NULL, delim);

  assert(strcmp(firstTok, "a") == 0);
  assert(strcmp(nextTok, "b") == 0);
  return 0;
}
