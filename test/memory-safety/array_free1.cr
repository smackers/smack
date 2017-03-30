#include <stdlib.h>
#include "smack.h"

// @flag --unroll=500
// @expect verified

#define MAXSIZE 5

typedef struct _DATA DATA, *PDATA;

struct _DATA {
  int *f;
  int x;
};

void free_array() {
  int i;
  DATA a[MAXSIZE];

  for (i = 0; i < MAXSIZE; i++) {
    a[i].f = (int*)malloc(sizeof(int));
    *(a[i].f) = 1;
    a[i].x = 2;
  }

  for (i = 0; i < MAXSIZE; i++) {
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

