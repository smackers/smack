#include "smack.h"
#include <assert.h>
#include <pthread.h>
#include <stdlib.h>

// @expect verified
// @flag --check=memory-safety

void *t1(void *arg) { return NULL; }

int main(void) {
  pthread_t tid1;
  pthread_create(&tid1, 0, t1, 0);
  pthread_join(tid1, NULL);
  return 0;
}
