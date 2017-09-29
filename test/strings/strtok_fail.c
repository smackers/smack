#include <string.h>
#include "smack.h"

// @flag --unroll=5
// @expect error

int main(void) {
  char *string = "a--";
  char *delim = "-";

  char *firstTok = strtok(string,delim);
  char *nextTok = strtok(NULL,delim);

  assert(strcmp(firstTok,"a") == 0);
  assert(strcmp(nextTok,"b") == 0);

  return 0;

}
