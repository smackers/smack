#include <stdlib.h>
#include "smack.h"

#define MAXSIZE 10

typedef struct _DATA DATA, *PDATA;

struct _DATA {
  int *f;
};

void free_array() {
  int i;
  DATA a[MAXSIZE];

  for (i = 0; i < MAXSIZE; i++) {
    a[i].f = (int*)malloc(sizeof(int));
    *(a[i].f) = 1;
  }

  for (i = 0; i < MAXSIZE; i++) {
    assert(*(a[i].f) == 1);
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

