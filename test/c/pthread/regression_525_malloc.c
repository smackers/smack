#include "smack.h"
#include <pthread.h>
#include <stdlib.h>

// @expect verified
// https://github.com/smackers/smack/issues/525

pthread_t tid1;
pthread_t tid2;

void *t1(void *arg) {
  int *x = malloc(sizeof(*x));
  if (!x)
    pthread_exit(NULL);
  *x = 1;
  pthread_exit(x);
  return NULL;
}

void *t2(void *arg) {
  int *y = malloc(sizeof(*y));
  if (!y)
    pthread_exit(NULL);
  *y = 2;
  pthread_exit(y);
  return NULL;
}

int main(void) {
  pthread_create(&tid1, 0, t1, 0);
  pthread_create(&tid2, 0, t2, 0);
  int *tid1_retval;
  int *tid2_retval;
  pthread_join(tid1, (void **)&tid1_retval);
  pthread_join(tid2, (void **)&tid2_retval);
  assert(!tid1_retval || *tid1_retval == 1);
  assert(!tid2_retval || *tid2_retval == 2);
  if (tid1_retval)
    free(tid1_retval);
  if (tid2_retval)
    free(tid2_retval);
  return 0;
}
