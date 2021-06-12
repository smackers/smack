#include "pthread.h"
#include "smack.h"
#include <assert.h>
#include <stdlib.h>
#include <string.h>

// @expect error
// @flag --unroll=6

const int SIGMA = 5;

int *array;
int array_index = 0;

void *thread(void *arg) {
  array[array_index] = 1;
  return 0;
}

int main() {
  int tid, sum;
  pthread_t *t;

  t = (pthread_t *)malloc(sizeof(pthread_t) * SIGMA);
  array = (int *)malloc(sizeof(int) * SIGMA);

  // assume(t);
  // assume(array);

  for (tid = 0; tid < SIGMA; tid++) {
    pthread_create(&t[tid], 0, thread, 0);
    array_index++;
  }

  for (tid = 0; tid < SIGMA; tid++) {
    pthread_join(t[tid], 0);
  }

  for (tid = sum = 0; tid < SIGMA; tid++) {
    sum += array[tid];
  }

  assert(sum == SIGMA); // <-- wrong, different threads might use the same array
                        // offset when writing

  return 0;
}
