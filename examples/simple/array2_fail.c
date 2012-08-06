#include <stdio.h>
#include <stdlib.h>
#include "smack.h"

#define MAXSIZE 50
#define RESET 0

int main() {
  int i = 0;
  int *a = (int*)malloc(MAXSIZE * sizeof(int));

  for (i = 0; i < MAXSIZE; i++) {
    __SMACK_invariant(0 <= i);
    __SMACK_invariant(i <= MAXSIZE);
    __SMACK_invariant(__SMACK_forall(__SMACK_x,  __SMACK_ARRAY_COUNT(a, sizeof(int), i), (*((int*)__SMACK_x)) == RESET));
    __SMACK_modifies(__SMACK_union(__SMACK_ARRAY_COUNT(a, sizeof(int), __SMACK_new(i)), __SMACK_set(&i)));
    
    a[i] = RESET;
  }

  __SMACK_assert(a[5] != RESET || a[50] == RESET);

  free(a);
  return 0;
}

