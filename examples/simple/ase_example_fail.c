#include <stdio.h>
#include <stdlib.h>
#include "smack.h"

typedef struct {
  int f1;
  int f2;
} Elem;

void __SMACK_anno_alloc(int size) {
  __SMACK_requires(size > 0);
  __SMACK_ensures(__SMACK_allocates(__SMACK_intToPtr(__SMACK_return)));
  __SMACK_ensures(__SMACK_size(__SMACK_intToPtr(__SMACK_return)) == size*sizeof(Elem));
  __SMACK_ensures(__SMACK_offsetOf(__SMACK_intToPtr(__SMACK_return)) == 0);
  TYPES(__SMACK_ensures(__SMACK_forall(__SMACK_x,
                                       __SMACK_ARRAY_COUNT(((Elem*)__SMACK_intToPtr(__SMACK_return)), sizeof(Elem), size),
                                       __SMACK_typeOf(__SMACK_x, TYPEP(Elem)))));
  INLINE(__SMACK_inline());
}
Elem* alloc(int size) {
  return (Elem*)malloc(size * sizeof(Elem));
}

void __SMACK_anno_init(int size) {
  __SMACK_requires(size > 0);
  INLINE(__SMACK_inline());
}
void init(int size) {
  int i;
  Elem *a1 = alloc(size);
  Elem *a2 = a1;

  for (i = 0; i < size; i++) {
    // *** loop invariants
    __SMACK_invariant(0 <= i);
    __SMACK_invariant(i <= size);
    __SMACK_invariant(__SMACK_forall(__SMACK_x,  __SMACK_ARRAY_COUNT(a1, sizeof(Elem), i), (((Elem*)__SMACK_x)->f1) == 1));
    INFER(__SMACK_modifies(__SMACK_union(__SMACK_addOffsetToSet(__SMACK_ARRAY_COUNT(a1, sizeof(Elem), __SMACK_new(i)), __SMACK_OFFSET(Elem, f1)),
                                         __SMACK_set(&i))));
    // ***

    a1[i].f1 = 1;
  }

  for (i = 0; i < size; i++) {
    // *** loop invariants
    __SMACK_invariant(0 <= i);
    __SMACK_invariant(i <= size);
    INFER(__SMACK_modifies(__SMACK_union(__SMACK_union(__SMACK_addOffsetToSet(__SMACK_ARRAY_COUNT(a1, sizeof(Elem), __SMACK_new(i)), __SMACK_OFFSET(Elem, f2)),
                                                       __SMACK_addOffsetToSet(__SMACK_ARRAY_COUNT(a2, sizeof(Elem), __SMACK_new(i)), __SMACK_OFFSET(Elem, f1))),
                                         __SMACK_set(&i))));
    // ***

    a1[i].f2 = 0;
    a2[i].f1 = 0;
  }

  for (i = 0; i < size; i++) {
    // *** loop invariants
    __SMACK_invariant(0 <= i);
    __SMACK_invariant(i <= size);
    INFER(__SMACK_modifies(__SMACK_set(&i)));
    // ***

    __SMACK_assert(a1[i].f1 == 1);
  }
}

int main() {
  init(10);
}

