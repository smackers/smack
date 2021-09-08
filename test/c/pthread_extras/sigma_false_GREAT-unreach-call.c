/* USEFUL - great example.  Looks like locked, but it isn't,
 *          since the array_index++ call in main can all happen
 *          at once, and THEN thread procedures run, so all
 *          get last array_index. (array_index==2)
 */

#include "pthread.h"
#include "smack.h"
#include <assert.h>
#include <stdlib.h>
#include <string.h>

// @expect error
// @flag --unroll=6

const int SIGMA = 5;

int *array;
int array_index = -1;
pthread_mutex_t lock;

void *thread(void *arg) {
  pthread_mutex_lock(&lock);
  int curidx = array_index;
  array[array_index] = 1;
  int cur = array[array_index];
  pthread_mutex_unlock(&lock);
  return 0;
}

int main() {
  int tid, sum;
  pthread_t *t;

  pthread_mutex_init(&lock, NULL);

  t = (pthread_t *)malloc(sizeof(pthread_t) * SIGMA);
  array = (int *)malloc(sizeof(int) * SIGMA);

  // assume(t);
  // assume(array);

  for (tid = 0; tid < SIGMA; tid++) {
    pthread_mutex_lock(&lock);
    pthread_create(&t[tid], 0, thread, 0);
    array_index++;
    pthread_mutex_unlock(&lock);
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
