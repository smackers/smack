#include "smack.h"
#include <assert.h>
#include <stdlib.h>

// @flag --loop-limit=11
// @flag --unroll=11
// @expect error

#define MAXSIZE 10

typedef struct _DATA DATA, *PDATA;

struct _DATA {
  int y;
  int *f;
  int x;
};

void free_array() {
  int i;
  DATA a[MAXSIZE];

  for (i = 0; i < MAXSIZE - 1; i++) {
    a[i].f = (int *)malloc(sizeof(int));
    *(a[i].f) = 1;
    a[i].x = 2;
    a[i].y = 3;
  }

  for (i = 0; i < MAXSIZE; i++) {
    assert(*(a[i].f) == 1);
    assert(a[i].x == 2);
    assert(a[i].y == 3);
    if (a[i].f != 0) {
      free(a[i].f);
      a[i].f = 0;
    }
  }
}

int main() {
  free_array();
  return 0;
}
