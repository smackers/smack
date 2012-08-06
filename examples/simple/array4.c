#include <stdio.h>
#include <stdlib.h>
#include "smack.h"

#define MAXSIZE 50
#define RESET 0

typedef struct {
  short data;
  int count;
  char status;
} elem;

void __SMACK_anno_initializeArray(elem *array) {
  TYPES(__SMACK_requires(__SMACK_forall(__SMACK_x,
                                        __SMACK_ARRAY_COUNT(array, sizeof(elem), MAXSIZE),
                                        __SMACK_typeOf(__SMACK_x, TYPEP(elem)))));
  __SMACK_requires(__SMACK_size(array) == MAXSIZE * sizeof(elem));
  __SMACK_requires(__SMACK_offsetOf(array) == 0);
  __SMACK_requires(__SMACK_allocated(array));
  __SMACK_ensures(__SMACK_forall(__SMACK_x, __SMACK_ARRAY_COUNT(array, sizeof(elem), MAXSIZE), (((elem*)__SMACK_x)->status) == RESET));
  INFER(__SMACK_modifies(__SMACK_addOffsetToSet(__SMACK_ARRAY_COUNT(array, sizeof(elem), MAXSIZE), (int)(((void*)&(array->status)) - ((void*)array)))));
  INLINE(__SMACK_inline());
}
void initializeArray(elem *array) {
  int i = 0;

  for (i = 0; i < MAXSIZE; i++) {
    // *** loop invariants
    __SMACK_invariant(0 <= i);
    __SMACK_invariant(i <= MAXSIZE);
    __SMACK_invariant(__SMACK_forall(__SMACK_x, __SMACK_ARRAY_COUNT(array, sizeof(elem), i), (((elem*)__SMACK_x)->status) == RESET));
    INFER(__SMACK_modifies(__SMACK_union(__SMACK_addOffsetToSet(__SMACK_ARRAY_COUNT(array, sizeof(elem), __SMACK_new(i)),
                                                                (int)(((void*)&(array->status)) - ((void*)array))),
                                         __SMACK_set(&i))));
    // ***

    array[i].status = RESET;
  }
}

int main() {
  int i = 0;
  elem *array = (elem*)malloc(MAXSIZE * sizeof(elem));

  initializeArray(array);

  for (i = 0; i < MAXSIZE; i++) {
    // *** loop invariants
    __SMACK_invariant(0 <= i);
    __SMACK_invariant(i <= MAXSIZE);
    INFER(__SMACK_modifies(__SMACK_set(&i)));
    // ***

    __SMACK_assert(array[i].status == RESET);
  }

  free(array);
  return 0;
}

