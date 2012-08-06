#include <stdio.h>
#include <stdlib.h>
#include "smack.h"

#define MAXSIZE 50
#define RESET 0
#define SET 1

void __SMACK_anno_resetArray(int *array) {
  TYPES(__SMACK_requires(__SMACK_forall(__SMACK_x,
                                        __SMACK_ARRAY_COUNT(array, sizeof(int), MAXSIZE),
                                        __SMACK_typeOf(__SMACK_x, TYPEP(int)))));
  __SMACK_requires(__SMACK_size(array) == MAXSIZE * sizeof(int));
  __SMACK_requires(__SMACK_offsetOf(array) == 0);
  __SMACK_requires(__SMACK_allocated(array));
  __SMACK_ensures(__SMACK_forall(__SMACK_x, __SMACK_ARRAY_COUNT(array, sizeof(int), MAXSIZE), (*((int*)__SMACK_x)) == RESET));
  __SMACK_modifies(__SMACK_ARRAY_COUNT(array, sizeof(int), MAXSIZE));
  INLINE(__SMACK_inline());
}
void resetArray(int *array) {
  int i = 0;

  for (i = 0; i < MAXSIZE; i++) {
    // *** loop invariants
    __SMACK_invariant(0 <= i);
    __SMACK_invariant(i <= MAXSIZE);
    __SMACK_invariant(__SMACK_forall(__SMACK_x, __SMACK_ARRAY_COUNT(array, sizeof(int), i), (*((int*)__SMACK_x)) == RESET));
    __SMACK_modifies(__SMACK_union(__SMACK_ARRAY_COUNT(array, sizeof(int), __SMACK_new(i)), __SMACK_set(&i)));
    // ***

    array[i] = RESET;
  }
}

void __SMACK_anno_setArray(int *array) {
  TYPES(__SMACK_requires(__SMACK_forall(__SMACK_x,
                                        __SMACK_ARRAY_COUNT(array, sizeof(int), MAXSIZE),
                                        __SMACK_typeOf(__SMACK_x, TYPEP(int)))));
  __SMACK_requires(__SMACK_size(array) == MAXSIZE * sizeof(int));
  __SMACK_requires(__SMACK_offsetOf(array) == 0);
  __SMACK_requires(__SMACK_allocated(array));
  __SMACK_ensures(__SMACK_forall(__SMACK_x, __SMACK_ARRAY_COUNT(array, sizeof(int), MAXSIZE), (*((int*)__SMACK_x)) == SET));
  __SMACK_modifies(__SMACK_ARRAY_COUNT(array, sizeof(int), MAXSIZE));
  INLINE(__SMACK_inline());
}
void setArray(int *array) {
  int i = 0;

  for (i = 0; i < MAXSIZE; i++) {
    // *** loop invariants
    __SMACK_invariant(0 <= i);
    __SMACK_invariant(i <= MAXSIZE);
    __SMACK_invariant(__SMACK_forall(__SMACK_x, __SMACK_ARRAY_COUNT(array, sizeof(int), i), (*((int*)__SMACK_x)) == SET));
    __SMACK_modifies(__SMACK_union(__SMACK_ARRAY_COUNT(array, sizeof(int), __SMACK_new(i)), __SMACK_set(&i)));
    // ***

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
    // *** loop invariants
    __SMACK_invariant(0 <= i);
    __SMACK_invariant(i <= MAXSIZE);
    __SMACK_modifies(__SMACK_set(&i));
    // ***

    __SMACK_assert(arrayOne[i] == RESET);
    __SMACK_assert(arrayTwo[i] == SET);
  }

  setArray(arrayOne);
  resetArray(arrayTwo);

  for (i = 0; i < MAXSIZE; i++) {
    // *** loop invariants
    __SMACK_invariant(0 <= i);
    __SMACK_invariant(i <= MAXSIZE);
    __SMACK_modifies(__SMACK_set(&i));
    // ***

    __SMACK_assert(arrayOne[i] == SET);
    __SMACK_assert(arrayTwo[i] == RESET);
  }

  free(arrayOne);
  free(arrayTwo);
  return 0;
}

