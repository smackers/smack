#ifndef PTHREADTYPES_H
#define PTHREADTYPES_H
#define _BITS_PTHREADTYPES_H	1

/* Mutex types.  */
enum
{
  PTHREAD_MUTEX_TIMED_NP,
  PTHREAD_MUTEX_RECURSIVE_NP,
  PTHREAD_MUTEX_ERRORCHECK_NP,
  PTHREAD_MUTEX_ADAPTIVE_NP,
  PTHREAD_MUTEX_NORMAL = PTHREAD_MUTEX_TIMED_NP,
  PTHREAD_MUTEX_RECURSIVE = PTHREAD_MUTEX_RECURSIVE_NP,
  PTHREAD_MUTEX_ERRORCHECK = PTHREAD_MUTEX_ERRORCHECK_NP,
  PTHREAD_MUTEX_DEFAULT = PTHREAD_MUTEX_NORMAL,
  PTHREAD_MUTEX_FAST_NP = PTHREAD_MUTEX_TIMED_NP
};

typedef int pthread_t;

#ifndef _PTHREAD_ATTR_T
#define _PTHREAD_ATTR_T
typedef int pthread_attr_t;
#endif

typedef struct{
  int prioceil, proto, pshared, type;
} pthread_mutexattr_t;

typedef struct{
  int lock, init;
  pthread_mutexattr_t attr;
} pthread_mutex_t;

typedef struct{
  int cond, init;
} pthread_cond_t;

typedef int pthread_condattr_t;

#endif
