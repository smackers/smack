//
// This file is distributed under the MIT License. See LICENSE for details.
//
#include "pthread.h"
#include "smack.h"

void *__SMACK_PthreadReturn[SMACK_MAX_THREADS];

void __SMACK_init_tidtype() {
#ifdef BIT_PRECISE
  __SMACK_top_decl("type $tidtype = bv32;");
#else
  __SMACK_top_decl("type $tidtype = i32;");
#endif
}

void __SMACK_init_func_corral_primitives() {
  // Declare these, so bpl parsing doesn't complain
  __SMACK_top_decl("procedure corral_getThreadID() returns (x:$tidtype);");
  __SMACK_top_decl("procedure corral_getChildThreadID() returns (x:$tidtype);");
}

void __SMACK_init_func_thread() {
  // Array and possible statuses for tracking pthreads
  __SMACK_top_decl("var $pthreadStatus: [$tidtype]int;");
  __SMACK_top_decl("const unique $pthread_uninitialized: int;");
  __SMACK_top_decl("const unique $pthread_initialized: int;");
  __SMACK_top_decl("const unique $pthread_waiting: int;");
  __SMACK_top_decl("const unique $pthread_running: int;");
  __SMACK_top_decl("const unique $pthread_stopped: int;");
  // Initialize this array so all threads begin as uninitialized
  __SMACK_code("assume (forall i:$tidtype :: $pthreadStatus[i] == "
               "$pthread_uninitialized);");
}

pthread_t pthread_self(void) {
  int tmp_tid = __VERIFIER_nondet_int();
  __SMACK_code("call @ := corral_getThreadID();", tmp_tid);
  __VERIFIER_assume(tmp_tid < SMACK_MAX_THREADS);

  // Print actual tid to SMACK traces
  int actual_tid = tmp_tid;

  return actual_tid;
}

int pthread_equal(pthread_t t1, pthread_t t2) {
  // Return non-zero if threads are equal.  0 otherwise.
  return (int)t1 == (int)t2;
}

int pthread_join(pthread_t __th, void **__thread_return) {
  pthread_t calling_tid = pthread_self();

  // Print the tid of the thread being joined to SMACK traces
  int joining_tid = __th;

  // Check for self-joining deadlock
  if (calling_tid == __th)
    return 35; // This is EDEADLK

  // Wait for the thread to terminate
  __SMACK_code("assume $pthreadStatus[@] == $pthread_stopped;", __th);

  if (__thread_return) {
    *__thread_return = __SMACK_PthreadReturn[__th];

    // Print return pointer value to SMACK traces
    void *actual_thread_return_pointer = *__thread_return;
  }

  return 0;
}

// TODO: A terminating thread that DOESN'T call pthread_exit() should have
//       an implicit call to pthread_exit().  This is not currently modeled.
//       Further, a child thread's routine which uses `return` calls should
//       have the returned value passed to this implicit call to pthread_exit().
//       In other words, a `return` should pass its value to an implicit call to
//       pthread_exit().
void pthread_exit(void *retval) {
  pthread_t tid = pthread_self();

// Ensure exit hasn't already been called
#ifndef DISABLE_PTHREAD_ASSERTS
  __SMACK_code("assert $pthreadStatus[@] == $pthread_running;", tid);
#endif
  __SMACK_PthreadReturn[tid] = retval;

  // Set return pointer value for display in SMACK traces
  void *pthread_return_pointer = retval;
}

int pthread_mutexattr_init(pthread_mutexattr_t *attr) {
  attr->type = PTHREAD_MUTEX_NORMAL;
  return 0;
}

int pthread_mutexattr_settype(pthread_mutexattr_t *attr, int type) {
  attr->type = type;
  return 0;
}

int pthread_mutex_init(pthread_mutex_t *mutex,
                       const pthread_mutexattr_t *attr) {
  // Can't check for already initialized error,
  //  since uninitialized values are nondet and could be INITIALIZED
  mutex->lock = UNLOCKED;
  mutex->init = INITIALIZED;
  if (attr == 0) {
    pthread_mutexattr_init(&mutex->attr);
  } else {
    mutex->attr.type = attr->type;
    // Any additional info modeled from attr should be copied,
    //  as changes to attr should not apply to mutexes alread initialized
    //  (as opposed to directly setting mutex->attr = attr)
  }
  return 0;
}

int pthread_mutex_lock(pthread_mutex_t *__mutex) {
  int tid = (int)pthread_self();
  // Ensure mutex is initialized & hasn't already been locked by caller
  if (__mutex->attr.type == PTHREAD_MUTEX_NORMAL) {
#ifndef DISABLE_PTHREAD_ASSERTS
    assert(__mutex->init == INITIALIZED);
    assert(__mutex->lock != tid);
#endif
  } else if (__mutex->attr.type == PTHREAD_MUTEX_ERRORCHECK) {
    if (__mutex->init != INITIALIZED)
      return 22; // This is EINVAL
    if (__mutex->lock == tid)
      return 35; // This is EDEADLK
  } else {
// Other types not currently implemented
#ifndef DISABLE_PTHREAD_ASSERTS
    assert(0);
#endif
  }
  __SMACK_code("call corral_atomic_begin();");
  // Wait for lock to become free
  __VERIFIER_assume(__mutex->lock == UNLOCKED);
  __mutex->lock = tid;
  __SMACK_code("call corral_atomic_end();");
  return 0;
}

int pthread_mutex_unlock(pthread_mutex_t *__mutex) {
  int tid = (int)pthread_self();
  // Ensure mutex is initialized & caller is current owner
  if (__mutex->attr.type == PTHREAD_MUTEX_NORMAL) {
#ifndef DISABLE_PTHREAD_ASSERTS
    assert(__mutex->init == INITIALIZED);
    assert(__mutex->lock == tid);
#endif
  } else if (__mutex->attr.type == PTHREAD_MUTEX_ERRORCHECK) {
    if (__mutex->init != INITIALIZED)
      return 22; // This is EINVAL
    if (__mutex->lock != tid)
      return 1; // This is EPERM
  } else {
// Other types not currently implemented
#ifndef DISABLE_PTHREAD_ASSERTS
    assert(0);
#endif
  }
  __SMACK_code("call corral_atomic_begin();");
  __mutex->lock = UNLOCKED;
  __SMACK_code("call corral_atomic_end();");
  return 0;
}

int pthread_mutex_destroy(pthread_mutex_t *__mutex) {
// Make sure the lock is initialized, and unlocked
#ifndef DISABLE_PTHREAD_ASSERTS
  assert(__mutex->init == INITIALIZED);
  assert(__mutex->lock == UNLOCKED);
#endif
  __SMACK_code("call corral_atomic_begin();");
  __mutex->init = UNINITIALIZED;
  __SMACK_code("call corral_atomic_end();");
  return 0;
}

int pthread_cond_init(pthread_cond_t *__cond, pthread_condattr_t *__condattr) {
  if (__condattr == 0) {
    __cond->cond = 0;
    __cond->init = INITIALIZED;
  } else {
// Unimplemented
// NOTE: if implemented, attr should be a copy of __condattr passed in
//       (spec says changes to condattr doesn't affect initialized conds
#ifndef DISABLE_PTHREAD_ASSERTS
    assert(0);
#endif
  }
  return 0;
}

int pthread_cond_wait(pthread_cond_t *__cond, pthread_mutex_t *__mutex) {
// Ensure conditional var is initialized, and mutex is locked properly
#ifndef DISABLE_PTHREAD_ASSERTS
  assert(__cond->init == INITIALIZED);
  assert((int)pthread_self() == __mutex->lock);
#endif
  pthread_mutex_unlock(__mutex);
  // Wait to be woken up
  // No need to check for signal on __cond, since OS can do spurious wakeup
  // Call to pthread_cond_wait should always be protected by while loop

  // Adding var checks in improves performance

  // assume(__cond->cond == 1);
  //__cond->cond = 0;
  pthread_mutex_lock(__mutex);
  return 0;
}

int pthread_cond_signal(pthread_cond_t *__cond) {
  // Do nothing, since state of __cond doesn't matter
  //  due to possibility of spurious wakeup from OS

  //__cond->cond = 1;
  return 0;
}

// NOTE: How to handle broadcast?  Technically, as is, all threads have
//       the opportunity to read __cond->cond before one of the other threads
//       switch this value back to 0...  I guess this is sufficient, but
//       will this require a high number of context switches for a true
//       broadcast to happen?
//
//       I thought about using cond->cond = 2 to signal broadcast, but then
//       how to know which thread to have switch it back to 0?

int pthread_cond_broadcast(pthread_cond_t *__cond) {
  // Do nothing, since state of __cond doesn't matter
  //  due to possibility of spurious wakeup from OS

  //__cond->cond = 1;
  return 0;
}

int pthread_cond_destroy(pthread_cond_t *__cond) {
// Make sure the cond is initialized
#ifndef DISABLE_PTHREAD_ASSERTS
  assert(__cond->init == INITIALIZED);
#endif
  __cond->init = UNINITIALIZED;
  return 0;
}

void __call_wrapper(pthread_t *__newthread, void *(*__start_routine)(void *),
                    void *__arg) {

  pthread_t ctid = pthread_self();
  // Wait for parent to set child's thread ID in original pthread_t struct
  __VERIFIER_assume(ctid == *__newthread);

  // Cycle through thread statuses properly, as thread is started, run,
  // and stopped.
  __SMACK_code("$pthreadStatus[@] := $pthread_waiting;", ctid);
  __SMACK_code("$pthreadStatus[@] := $pthread_running;", ctid);
  __start_routine(__arg);
  __SMACK_code("$pthreadStatus[@] := $pthread_stopped;", ctid);
}

int pthread_create(pthread_t *__newthread, __const pthread_attr_t *__attr,
                   void *(*__start_routine)(void *), void *__arg) {

  // Add unreachable C-level call to __call_wrapper, so LLVM sees
  // the call to __call_wrapper and performs DSA on it.
  int x = __VERIFIER_nondet_int();
  __VERIFIER_assume(x == 0);
  if (x)
    __call_wrapper(__newthread, __start_routine, __arg);

  __SMACK_code("async call @(@, @, @);", __call_wrapper, __newthread,
               __start_routine, __arg);
  pthread_t tmp = __VERIFIER_nondet_int();
  __SMACK_code("call @ := corral_getChildThreadID();", tmp);
  __VERIFIER_assume(tmp < SMACK_MAX_THREADS);
  *__newthread = tmp;

  return 0;
}
