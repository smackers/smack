#include "smack.h"
#include <assert.h>
#include <string.h>

// @expect verified

int main(void) {
  char *large = "wxyz";
  char *small = "xy";
  char *firstOccurrenceOfXY = strstr(large, small);

  assert(strcmp(firstOccurrenceOfXY, "xyz") == 0);
  return 0;
}
