// Tests with multiple threads

// @expect error

#include <pthread.h>
#include <smack.h>

pthread_mutex_t lock = PTHREAD_MUTEX_INITIALIZER;

int x = 1;

void *t1(void *arg) {
  pthread_mutex_lock(&lock);
  x++;
  pthread_mutex_unlock(&lock);
}

void *t2(void *arg) {
  x++;
}

int main() {

  pthread_t tid1, tid2;

  pthread_create(&tid1, 0, t1, 0);
  pthread_create(&tid2, 0, t2, 0);
  pthread_mutex_lock(&lock);
  x++;
  pthread_mutex_unlock(&lock);
  pthread_join(tid1, 0);
  pthread_join(tid2, 0);
  assert(x == 4);
}
