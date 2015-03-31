// Not useful - uses strcpy, has disallowed (by svcomp) malloc fail

//extern void __VERIFIER_error() __attribute__ ((__noreturn__));
#define __VERIFIER_error() assert(0)

#include <pthread.h>
#include <stdlib.h>
#include <string.h>

void __VERIFIER_assert(int expression) { if (!expression) { ERROR: __VERIFIER_error();}; return; }

char *v;

void *thread1(void * arg)
{
  v = malloc(sizeof(char) * 8);
}

void *thread2(void *arg)
{
  if (v) strcpy(v, "Bigshot");
}


int main()
{
  __SMACK_code("assume (forall i:int :: $pthreadStatus[i][0] == $pthread_uninitialized);"); 

  pthread_t t1, t2;

  pthread_create(&t1, 0, thread1, 0);
  pthread_join(t1, 0);

  pthread_create(&t2, 0, thread2, 0);
  pthread_join(t2, 0);

  __VERIFIER_assert(v[0] == 'B');  // <---- wrong, malloc() can fail and therefore no strcpy! Competition's rule: malloc() never fails, thus it is safe.

  return 0;
}

