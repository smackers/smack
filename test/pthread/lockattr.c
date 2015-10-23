// Uses error handling from error checking mutex
// to avoid what would otherwise be deadlock or permitted error

// @expect verified

#include <pthread.h>
#include <smack.h>

pthread_mutex_t lock;
pthread_mutexattr_t lockattr;
int x;

void* t1(void *arg) {
  int err = __SMACK_nondet();
  pthread_mutex_lock(&lock);
  err = pthread_mutex_lock(&lock);
  // Should be an EDEADLK error
  assert(35 == err);
  x++;
  pthread_mutex_unlock(&lock);
  err = pthread_mutex_unlock(&lock);
  // Should be an EPERM error
  assert(1 == err);
}

int main() {
  x = 0;
  lock.attr.type = PTHREAD_MUTEX_ERRORCHECK;
  int err = pthread_mutex_lock(&lock);
  // Should be an EINVAL error
  assert(err = 22);
  err = 0;
  err = pthread_mutex_unlock(&lock);
  // Should be an EINVAL error
  assert(err = 22);
  pthread_mutexattr_init(&lockattr);
  pthread_mutexattr_settype(&lockattr, PTHREAD_MUTEX_ERRORCHECK);
  pthread_mutex_init(&lock, &lockattr);
  pthread_t t;
  pthread_create(&t, 0, t1, 0);
  pthread_join(t, 0);
  assert(x==1);
}
