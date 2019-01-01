#include <string.h>
#include "smack.h"

// @expect error

int main(void) {
  char *large = "lmno";
  char *small = "xy";
  char *firstOccurrenceOfXY = strstr(large,small);

  assert(firstOccurrenceOfXY != 0);
  return 0;
}
