#include "pthread.h"
#include "smack.h"
#include <stdio.h>

// @expect verified
// @flag --unroll=3

int num;

pthread_mutex_t m;
pthread_cond_t empty, full;

void *thread1(void *arg) {
  pthread_mutex_lock(&m);

  while (num > 0)
    pthread_cond_wait(&empty, &m);

  num++;

  pthread_mutex_unlock(&m);
  pthread_cond_signal(&full);
}

void *thread2(void *arg) {
  pthread_mutex_lock(&m);

  while (num == 0)
    pthread_cond_wait(&full, &m);

  num--;

  pthread_mutex_unlock(&m);

  pthread_cond_signal(&empty);
}

int main() {
  pthread_t t1, t2;

  num = 1;

  pthread_mutex_init(&m, 0);
  pthread_cond_init(&empty, 0);
  pthread_cond_init(&full, 0);

  pthread_create(&t1, 0, thread1, 0);
  pthread_create(&t2, 0, thread2, 0);

  pthread_join(t1, 0);
  pthread_join(t2, 0);

  assert(num == 1);

  return 0;
}
