
#include <string.h>
#include "smack.h"

// @flag --unroll=5
// @expect verified

int main() {

  char *string = "a-b";
  char *delim = "-";

  char *firstTok = strtok(string,delim);
  char *nextTok = strtok(NULL,delim);

  assert(strcmp(firstTok,"a") == 0);
  assert(strcmp(nextTok,"b") == 0);

  return 0;

}
