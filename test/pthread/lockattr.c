// Uses error handling from error checking mutex
//  to avoid what would otherwise be deadlock or permitted error

#include <pthread.h>

pthread_mutex_t lock;
pthread_mutexattr_t lockattr;
int x;

void* t1(void *arg) {
  int err = __SMACK_nondet();
  pthread_mutex_lock(&lock);
  err = pthread_mutex_lock(&lock);
  if(35 != err) {
    // Should be an EDEADLK error
    assert(0);
  }
  x++;
  pthread_mutex_unlock(&lock);
  err = pthread_mutex_unlock(&lock);
  if(1 != err) {
    // Should be an EPERM error
    assert(0);
  }
}

int main() {
  x = 0;
  pthread_mutexattr_init(&lockattr);
  pthread_mutexattr_settype(&lockattr, PTHREAD_MUTEX_ERRORCHECK);
  pthread_mutex_init(&lock, &lockattr);
  pthread_t t;
  pthread_create(&t, 0, t1, 0);
  pthread_join(t, 0);
  assert(x==1);
}
