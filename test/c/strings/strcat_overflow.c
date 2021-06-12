#include "smack.h"
#include <assert.h>
#include <string.h>

// @flag --check=memory-safety
// @expect error

int main(void) {
  char notLong[3] = "So";
  char *moreText = "..";
  char *overflowed = strcat(notLong, moreText);

  assert(strcmp(overflowed, "So..") == 0);
  return 0;
}
