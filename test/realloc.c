#include <stdlib.h>
#include <string.h>
#include "smack.h"

/* void *realloc2(void *src, unsigned long long new_size) {
  if (src == NULL && new_size != 0) {
    return malloc(new_size);
  }
  if (src != NULL && new_size == 0) {
    return src;
  }
  void *result = malloc(new_size);
  memcpy(result, src, new_size);
  return result;
  } */

int main() {
  {
    // Tests that epanding an allocated memory region properly copies
    // the contents of the array up to the old size of the array.
    int *x = malloc(sizeof(int));
    x[0] = 0;
    assert(x[0] == 0);
    
    int *nx = realloc(x, 2*sizeof(int)); // Expanding array
    if (nx == NULL) {
      free(x);
      return 0;
    }
    x = nx;
    assert(x[0] == 0); // Should pass, but smack treats as non-det
                       // because copying isn't modeled
    free(nx);
  }
  {
    // Tests that realloc of the NULL pointer is the same as malloc.
    // Tests that malloc between two realloc calls leaves the memory in
    // the realloc'd array is copied properly.

    int *y = realloc(NULL, sizeof(int)); // Should allocate
    *y = 1;
    int *x = malloc(sizeof(int));
    *x = 2;
    int *ny = realloc(y, 2*sizeof(int)); // Should make y bigger
    if (ny == NULL) {
      free(y);
      free(x);
      return 0;
    }

    y = ny;
    y[1] = 3;

    assert(y[0] == 1); // Make sure old contents were copied correctly
    assert(y[1] == 3);
  }
  {
    // Tests that shrinking an allocated memory region properly copies
    // the contents of the array up to the new size of the array.
    int *x = malloc(2*sizeof(int));
    x[0] = 0;
    x[1] = 1;
    assert(x[0] == 0);
    assert(x[1] == 1);
    
    int *nx = realloc(x, sizeof(int)); // The first element should be copied.
    if (nx == NULL) {
      free(x);
      return 0;
    }
    x = nx;
    assert(x[0] == 0); // Should pass, but smack treats as non-det because
                       // copying isn't modeled
    free(nx);    
  }
  int *seven = realloc(NULL, 30);
  seven[3] = 7;
  assert(seven[3] == 7);
  
}
