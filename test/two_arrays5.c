#include <stdio.h>
#include <stdlib.h>
#include "smack.h"

#define RESET 0
#define SET 1

typedef struct {
  short data;
  int count;
  char status;
} elem;

int arraySize;

void resetArray(elem *array) {
  int i = 0;

  for (i = 0; i < arraySize; i++) {
    array[i].status = RESET;
  }
}

void setArray(elem *array) {
  int i = 0;

  for (i = 0; i < arraySize; i++) {
    array[i].status = SET;
  }
}

void initializeCount(elem *array) {
  int i = 0;

  for (i = 0; i < arraySize; i++) {
    array[i].count = 0;
  }
}

int main() {
  arraySize = __SMACK_nondet();
  assume(arraySize > 0);

  elem *arrayOne = (elem*)malloc(arraySize * sizeof(elem));
  elem *arrayTwo = (elem*)malloc(arraySize * sizeof(elem));

  resetArray(arrayOne);
  setArray(arrayTwo);
  initializeCount(arrayTwo);

  initializeCount(arrayOne);
  setArray(arrayOne);
  resetArray(arrayTwo);

  free(arrayOne);
  free(arrayTwo);
  return 0;
}

