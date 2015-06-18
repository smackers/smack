// This file should have a race since only the callee thread is locking
//  before doing x++

// @expect error

#include <pthread.h>

pthread_mutex_t lock = PTHREAD_MUTEX_INITIALIZER;

int x = 1;

void *t1(void *arg) {
  pthread_mutex_lock(&lock);
  x++;
  pthread_mutex_unlock(&lock);
}

int main() {

  pthread_t t;

  pthread_create(&t, 0, t1, 0);
  x++;
  pthread_join(t, 0);
  assert(x == 3);
  

}
