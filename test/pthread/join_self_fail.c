// Tests deadlock detection when join on self

// @expect error

#include <pthread.h>
#include <smack.h>

////////////////////////////////////////////////////////////////
// 
// Declare alternate functions for pthread_join(),
// __call_wrapper(), and pthread_create(), to illustrate
// failure when `assume(ctid == *__newthread)` is not present
// in __call_wrapper().
//
// Definitions are found in this file, below the benchmark
//
////////////////////////////////////////////////////////////////
int pthread_join2(pthread_t __th, void **__thread_return);
void __call_wrapper2(pthread_t *__restrict __newthread,
                     void *(*__start_routine) (void *),
                     void *__restrict __arg);
int pthread_create2(pthread_t *__restrict __newthread,
                    __const pthread_attr_t *__restrict __attr,
                    void *(*__start_routine) (void *),
                    void *__restrict __arg);
////////////////////////////////////////////////////////////////
// Begin benchmark:
////////////////////////////////////////////////////////////////

pthread_mutex_t lock = PTHREAD_MUTEX_INITIALIZER;

void* t1(void* arg) {
  pthread_t* selfptr = (pthread_t*)arg;
  pthread_t self = *selfptr;
  int ret;
  int err = pthread_join2(self, (void*)&ret);
  // Should be an EDEADLK error
  assert(err == 35);
  if(err != 35)
    assert(0);

  pthread_exit((void*)1);
  return 0;
}

int main() {
  pthread_t tid1 = __VERIFIER_nondet_int();
  int ret;
  pthread_create2(&tid1, 0, t1, &tid1);
  return 0;
}

////////////////////////////////////////////////////////////////
// End benchmark
////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////
//
// Below are alternate definitions for pthread_join(),
// __call_wrapper(), and pthread_create(), to illlustrate
// failure when `assume(ctid == *__newthread)` is not present
// in __call_wrapper().
//
////////////////////////////////////////////////////////////////
int pthread_join2(pthread_t __th, void **__thread_return) {
  pthread_t calling_tid = pthread_self();

  // Print the tid of the thread being joined to SMACK traces
  int joining_tid = __th;

  // Check for self-joining deadlock
  if(calling_tid == __th)
    return 35;    // This is EDEADLK

  // When verifying join_self.c, this next `assert(0)` should never be
  // reached if the pthread model is correct beacuse calling_tid should
  // be equal to __th in this function, so the if branch should always
  // be taken, returning 35.
  //
  // However, when `assume(ctid == *__newthread)` is not present in 
  // __call_wrapper(), then it is possible that parent thread hasn't set
  // the child thread ID in the original pthread_t struct, so calling_tid
  // won't match the passed in argument, __th, and so this assert(0) is 
  // reachable in this case (of course, this is all specifically for 
  // join_self()).
  assert(0);

  // Wait for the thread to terminate
  __SMACK_code("assume $pthreadStatus[@][0] == $pthread_stopped;", __th);

  // Get the thread's return value
  void* tmp_thread_return_pointer = (void*)__VERIFIER_nondet_long();
  __SMACK_code("@ := $pthreadStatus[@][1];", tmp_thread_return_pointer, __th);
  *__thread_return = tmp_thread_return_pointer;

  // Print return pointer value to SMACK traces
  void* actual_thread_return_pointer = *__thread_return;

  return 0;
}

void __call_wrapper2(pthread_t *__restrict __newthread,
                    void *(*__start_routine) (void *),
                    void *__restrict __arg) {

  pthread_t ctid = pthread_self();
  // This next line is commented to demonstrate failure of pthread_join()
  // to detect a self-join deadlock when child thread does not wait for
  // parent thread to properly record the child thread's ID in the original
  // pthread_t struct.
  //assume(ctid == *__newthread);
  
  // I think Zvonimir proposed to just use ctid to index into $pthreadStatus
  // This would work in most situations, HOWEVER, what if the parameter __arg
  // points to __newthread?  Then, __start_routine() could modify this
  // object before the parent thread sets __newthread to the ctid.
  __SMACK_code("$pthreadStatus[@][0] := $pthread_waiting;", ctid);

  __SMACK_code("$pthreadStatus[@][0] := $pthread_running;", ctid);
  __start_routine(__arg);
  __SMACK_code("$pthreadStatus[@][0] := $pthread_stopped;", ctid);
}

int pthread_create2(pthread_t *__restrict __newthread,
                   __const pthread_attr_t *__restrict __attr,
                   void *(*__start_routine) (void *),
                   void *__restrict __arg) {

  pthread_t tmp = __VERIFIER_nondet_int();

  // Add unreachable C-level call to __call_wrapper, so llvm sees
  // the call to __call_wrapper and performs DSA on it.
  int x = __VERIFIER_nondet_int();
  assume(x == 0);
  if(x) __call_wrapper2(__newthread, __start_routine, __arg);

  __SMACK_code("async call @(@, @, @);",
               __call_wrapper2, __newthread,
               __start_routine, __arg);
  __SMACK_code("call @ := corral_getChildThreadID();", tmp);
  *__newthread = tmp;

  return 0;
}





