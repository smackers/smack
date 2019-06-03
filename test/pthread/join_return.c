#include <pthread.h>
#include <smack.h>
#include <stdlib.h>

// Tests join & return in general - would fail if join doesn't block.
// Also tests that exit and join successfully store/load a return value
// and that return values work when pointers.

// @expect verified

int x = 1;

typedef struct pair {
  int x;
  int y;
} pair;

void *t1(void *arg) {
  x++;
  pair *retptr = (pair *)malloc(sizeof(pair));
  retptr->x = 3;
  retptr->y = 4;
  pthread_exit(retptr);
  return 0;
}

int main(void) {
  pthread_t t;
  pair *ret;

  pthread_create(&t, 0, t1, 0);
  pthread_join(t, &ret);
  assert(x == 2);
  assert(ret->x == 3);
  assert(ret->y == 4);
  free(ret);
  return 0;
}
