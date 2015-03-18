// Generally tests pthread_cond_wait, pthread_cond_signal,
//  pthread_cond_init

#include <pthread.h>

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
  pthread_exit(NULL);
}

void *j2(void *arg) {
  pthread_mutex_lock(&lock);
  while(!thread1Done)
    pthread_cond_wait(&cond, &lock);
  assert(count==1);
  pthread_mutex_unlock(&lock);
  pthread_exit(NULL);
}

int main() {
  pthread_t t1, t2;
  pthread_cond_init(&cond, NULL);
  pthread_mutex_init(&lock, NULL);
  pthread_create(&t1, NULL, j1, NULL);
  pthread_create(&t2, NULL, j2, NULL);
  pthread_join(t1, NULL);
  pthread_join(t2, NULL);
  return 0;
}
