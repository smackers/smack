#include <stdio.h>
#include <stdlib.h>
#include "smack.h"

#define MAXSIZE 50

int x;

void __SMACK_GlobalInvariant() {
  __SMACK_invariant(__SMACK_allocated(&x));
  TYPES(__SMACK_invariant(__SMACK_typeOf(&x, TYPEP(int))));
}

void __SMACK_anno_main() {
  __SMACK_modifies(__SMACK_set(&x));
}
int main() {
  int i = 0;

  x = 0;

  for (i = 0; i < MAXSIZE; i++) {
    __SMACK_invariant(0 <= i);
    __SMACK_invariant(i <= MAXSIZE);
    __SMACK_invariant(x < MAXSIZE);
    __SMACK_modifies(__SMACK_union(__SMACK_set(&x), __SMACK_set(&i)));

    x = i;
  }
  return 0;
}

