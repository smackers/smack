#include <stdio.h>
#include <stdlib.h>
#include "smack.h"

// @expect error

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

  for (i = arraySize - 1; i >= 0; i--) {
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
  int i = 0;
  elem *arrayOne;
  elem *arrayTwo;

  arraySize = __VERIFIER_nondet_int();
  assume(arraySize > 0);

  arrayOne = (elem*)malloc(arraySize * sizeof(elem));
  arrayTwo = (elem*)malloc(arraySize * sizeof(elem));

  resetArray(arrayOne);
  setArray(arrayTwo);
  initializeCount(arrayTwo);

  for (i = 0; i < arraySize; i++) {
    assert(arrayOne[i].status == RESET);
    assert(arrayTwo[i].status == SET);
    assert(arrayTwo[i].count == 0);
  }

  initializeCount(arrayOne);
  setArray(arrayOne);
  resetArray(arrayTwo);

  for (i = arraySize - 1; i >= 0; i--) {
    assert(arrayOne[i].count != 0 || arrayOne[i].status != SET || arrayTwo[i].status != RESET);
  }

  free(arrayOne);
  free(arrayTwo);
  return 0;
}

