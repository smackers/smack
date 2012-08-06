#include <stdlib.h>
#include "smack.h"

#define MAXSIZE 42

typedef struct _DATA DATA, *PDATA;

struct _DATA {
  int *f;
  int x;
};

DATA a[MAXSIZE];

void __SMACK_anno_free_array() {
  TYPES(__SMACK_requires(__SMACK_forall(__SMACK_x,
                                        __SMACK_ARRAY_COUNT(a, sizeof(DATA), MAXSIZE),
                                        __SMACK_typeOf(__SMACK_x, TYPEP(DATA)))));
  __SMACK_requires(__SMACK_forall(__SMACK_x,
                                  __SMACK_ARRAY_COUNT(a, sizeof(DATA), MAXSIZE),
                                  __SMACK_or(((DATA*)__SMACK_x)->f == NULL, __SMACK_allocated(((DATA*)__SMACK_x)->f))));
  __SMACK_requires(__SMACK_forall(__SMACK_x,
                                  __SMACK_ARRAY_COUNT(a, sizeof(DATA), MAXSIZE),
                                  __SMACK_objectOf(((DATA*)__SMACK_x)->f) != __SMACK_objectOf(a)));
  __SMACK_requires(__SMACK_uniqueDeref(FIELDP(DATA, f),
                                       __SMACK_addOffsetToSet(__SMACK_ARRAY_COUNT(a, sizeof(DATA), MAXSIZE), __SMACK_OFFSET(DATA,f))));
  __SMACK_requires(__SMACK_forall(__SMACK_x, __SMACK_ARRAY_COUNT(a, sizeof(DATA), MAXSIZE), __SMACK_offsetOf(((DATA*)__SMACK_x)->f) == 0));
  __SMACK_frees(__SMACK_setDeref(FIELDP(DATA, f),
                                 __SMACK_addOffsetToSet(__SMACK_ARRAY_COUNT(a, sizeof(DATA), MAXSIZE), __SMACK_OFFSET(DATA,f))));
  __SMACK_modifies(__SMACK_addOffsetToSet(__SMACK_ARRAY_COUNT(a, sizeof(DATA), MAXSIZE), __SMACK_OFFSET(DATA,f)));
  INLINE(__SMACK_inline());
}
void free_array() {
  int i;
  
  for (i = 0; i < MAXSIZE; i++) {
    __SMACK_invariant(0 <= i);
    __SMACK_invariant(i <= MAXSIZE);
    __SMACK_frees(__SMACK_setDeref(FIELDP(DATA, f),
                                   __SMACK_addOffsetToSet(__SMACK_ARRAY_COUNT(a, sizeof(DATA), __SMACK_new(i)), __SMACK_OFFSET(DATA,f))));
    __SMACK_modifies(__SMACK_addOffsetToSet(__SMACK_ARRAY_COUNT(a, sizeof(DATA), __SMACK_new(i)), __SMACK_OFFSET(DATA,f)));
    __SMACK_modifies(__SMACK_set(&i));

    if (a[i].f != 0) {
      free(a[i].f);
      a[i].f = 0;
    }
  }
}

int main() {
  return 0;
}

