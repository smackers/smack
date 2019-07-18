#include "smack.h"
#include <stdlib.h>

// @expect error

#define MAXSIZE 10
#define RESET 0

int main() {
  int *a = (int *)malloc(MAXSIZE * sizeof(int));

  free(a);
  free(a);
  return 0;
}
