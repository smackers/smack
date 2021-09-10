#include "smack.h"
#include <assert.h>
#include <string.h>

// @expect verified

int main(void) {
  char brick[10];
  strcpy(brick, "bl");
  char *glue = "ue";
  char *modernart = strcat(brick, glue);

  assert(strcmp(modernart, "blue") == 0);
  return 0;
}
