#include <stdio.h>
#include <stdlib.h>
#include "smack.h"

#define MAXSIZE 10
#define RESET 0

typedef struct {
  short data;
  int count;
  char status;
} elem;

void initializeArray(elem *array) {
  int i = 0;

  for (i = 0; i < MAXSIZE; i++) {
    array[i].status = RESET;
  }
}

int main() {
  int i = 0;
  elem *array = (elem*)malloc((MAXSIZE + 1) * sizeof(elem));

  initializeArray(array);

  for (i = 0; i < MAXSIZE + 1; i++) {
    assert(array[i].status == RESET);
  }

  free(array);
  return 0;
}

