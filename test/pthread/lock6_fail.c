// Tests that locks are independent

// @expect error

#include <pthread.h>

pthread_mutex_t lock1 = PTHREAD_MUTEX_INITIALIZER;
pthread_mutex_t lock2 = PTHREAD_MUTEX_INITIALIZER;

int x = 1;

void *t1(void *arg) {
  pthread_mutex_lock(&lock1);
  x++;
  pthread_mutex_unlock(&lock1);
}

void *t2(void *arg) {
  pthread_mutex_lock(&lock2);
  x++;
  pthread_mutex_unlock(&lock2);
}

int main() {

  pthread_t tid1, tid2, tid3, tid4;
  assert(lock1.lock == UNLOCKED);
  assert(lock1.init == INITIALIZED);
  assert(lock2.lock == UNLOCKED);
  assert(lock2.init == INITIALIZED);

  pthread_create(&tid1, 0, t1, 0);
  pthread_create(&tid2, 0, t2, 0);
  pthread_mutex_lock(&lock1);
  x++;
  pthread_mutex_unlock(&lock1);
  pthread_mutex_lock(&lock2);
  x++;
  pthread_mutex_unlock(&lock2);
  pthread_join(tid1, 0);
  pthread_join(tid2, 0);
  assert(x == 5);
}
