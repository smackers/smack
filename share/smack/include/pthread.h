//
// Copyright (c) 2013 Zvonimir Rakamaric (zvonimir@cs.utah.edu),
//                    Michael Emmi (michael.emmi@gmail.com)
// This file is distributed under the MIT License. See LICENSE for details.
//
#ifndef PTHREAD_H
#define PTHREAD_H

// Include pthreadtypes.h
#include "pthreadtypes.h"

//model mutex:
//  0 = unlocked,
//  else = locked by thread with matching id

#define UNLOCKED 0
#define UNINITIALIZED 0
#define INITIALIZED 1
//  !!!!! ERROR HERE? - if mutex already initialized, behavior
//        of initialization should be undefined
#define PTHREAD_MUTEX_INITIALIZER {UNLOCKED, INITIALIZED}

//Declare corral primitive procedures
//__SMACK_INIT(corral_primitives);

// Initialize thread status tracking variables (OS level behavior)
//__SMACK_INIT(thread);

void __VERIFIER_atomic_begin();

void __VERIFIER_atomic_end();

pthread_t pthread_self(void);

int pthread_equal(pthread_t t1, pthread_t t2);

int pthread_join(pthread_t __th, void **__thread_return);

void pthread_exit(void *retval);

int pthread_mutexattr_init(pthread_mutexattr_t *attr);

int pthread_mutexattr_settype(pthread_mutexattr_t *attr, int type);

int pthread_mutex_init(pthread_mutex_t *mutex, const pthread_mutexattr_t *attr);

int pthread_mutex_lock(pthread_mutex_t *__mutex);

int pthread_mutex_unlock(pthread_mutex_t *__mutex);

int pthread_mutex_destroy(pthread_mutex_t *__mutex);

int pthread_cond_init(pthread_cond_t *__cond, pthread_condattr_t *__condattr);

int pthread_cond_wait(pthread_cond_t *__cond, pthread_mutex_t *__mutex);

int pthread_cond_signal(pthread_cond_t *__cond);

// NOTE: How to handle broadcast?  Technically, as is, all threads have
//       the opportunity to read __cond->cond before one of the other threads
//       switch this value back to 0...  I guess this is sufficient, but
//       will this require a high number of context switches for a true
//       broadcast to happen?
//
//       I thought about using cond->cond = 2 to signal broadcast, but then
//       how to know which thread to have switch it back to 0?

int pthread_cond_broadcast(pthread_cond_t *__cond);

int pthread_cond_destroy(pthread_cond_t *__cond);

void __call_wrapper(pthread_t *__restrict __newthread, void *(*__start_routine) (void *), void *__restrict __arg);

int pthread_create(pthread_t *__restrict __newthread, __const pthread_attr_t *__restrict __attr, void *(*__start_routine) (void *), void *__restrict __arg);

#endif // PTHREAD_H
