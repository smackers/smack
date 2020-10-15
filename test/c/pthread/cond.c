#include "smack.h"
#include <assert.h>
#include <pthread.h>

// Generally tests pthread_cond_wait, pthread_cond_signal,
// pthread_cond_init

// @expect verified

pthread_cond_t cond;
pthread_mutex_t lock;
int thread1Done = 0;
int count = 0;

void *j1(void *arg) {
  pthread_mutex_lock(&lock);
  count++;
  thread1Done = 1;
  pthread_cond_signal(&cond);
  pthread_mutex_unlock(&lock);
  pthread_exit(0);
  return 0;
}

void *j2(void *arg) {
  pthread_mutex_lock(&lock);
  while (!thread1Done)
    pthread_cond_wait(&cond, &lock);
  assert(count == 1);
  pthread_mutex_unlock(&lock);
  pthread_exit(0);
  return 0;
}

int main(void) {
  pthread_t t1, t2;
  pthread_cond_init(&cond, 0);
  pthread_mutex_init(&lock, 0);
  assert(lock.init == INITIALIZED);
  pthread_create(&t1, 0, j1, 0);
  pthread_create(&t2, 0, j2, 0);
  pthread_join(t1, 0);
  pthread_join(t2, 0);
  return 0;
}
