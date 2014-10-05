#include <stdio.h>
#include <stdlib.h>
#include "smack.h"

#define MAXSIZE 10
#define RESET 0
#define SET 1

void resetArray(int *array) {
  int i = 0;

  for (i = 0; i < MAXSIZE; i++) {
    array[i] = RESET;
  }
}

void setArray(int *array) {
  int i = 0;

  for (i = 0; i < MAXSIZE; i++) {
    array[i] = SET;
  }
}

int main() {
  int i = 0;
  int *arrayOne = (int*)malloc(MAXSIZE * sizeof(int));
  int *arrayTwo = (int*)malloc(MAXSIZE * sizeof(int));

  resetArray(arrayOne);
  setArray(arrayTwo);

  for (i = 0; i < MAXSIZE; i++) {
    assert(arrayOne[i] == RESET);
    assert(arrayTwo[i] == SET);
  }

  setArray(arrayOne);
  resetArray(arrayTwo);

  for (i = 0; i < MAXSIZE; i++) {
    assert(arrayOne[i] == SET);
    assert(arrayTwo[i] == RESET);
  }

  free(arrayOne);
  free(arrayTwo);
  return 0;
}

