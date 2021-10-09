/* Testcase from Threader's distribution. For details see:
   http://www.model.in.tum.de/~popeea/research/threader
*/

#include "pthread.h"
#include "smack.h"
#include <assert.h>

// @expect verified

#define inode int // the lock
#define file int
#define scull_dev int
#define scull_qset_type int
#define loff_t int
#define ssize_t int
#define size_t int
#define unsigned_long int
#define unsigned_int int
#define char int
#define void_ptr int

#define tid1 1
#define tid2 2

#define FILE_WITH_LOCK_UNLOCKED 0
// from include/linux/errno.h
#define ERESTARTSYS 512
// from kern/include/kern/errno.h
#define EFAULT 2
#define ENOMEM 4
#define ENOTTY 25
#define EINVAL 28
#define SCULL_QUANTUM 4000
#define SCULL_QSET 1000
#define _IOW(i, n, t) n
#define _IO(i, n) n
#define _IOR(i, n, t) n
#define _IOWR(i, n, t) n

/*
 * Ioctl definitions
 */

/* Use 'k' as magic number */
#define SCULL_IOC_MAGIC 'k'
/* Please use a different 8-bit number in your code */

#define SCULL_IOCRESET _IO(SCULL_IOC_MAGIC, 0)

/*
 * S means "Set" through a ptr,
 * T means "Tell" directly with the argument value
 * G means "Get": reply by setting through a pointer
 * Q means "Query": response is on the return value
 * X means "eXchange": switch G and S atomically
 * H means "sHift": switch T and Q atomically
 */
#define SCULL_IOCSQUANTUM _IOW(SCULL_IOC_MAGIC, 1, int)
#define SCULL_IOCSQSET _IOW(SCULL_IOC_MAGIC, 2, int)
#define SCULL_IOCTQUANTUM _IO(SCULL_IOC_MAGIC, 3)
#define SCULL_IOCTQSET _IO(SCULL_IOC_MAGIC, 4)
#define SCULL_IOCGQUANTUM _IOR(SCULL_IOC_MAGIC, 5, int)
#define SCULL_IOCGQSET _IOR(SCULL_IOC_MAGIC, 6, int)
#define SCULL_IOCQQUANTUM _IO(SCULL_IOC_MAGIC, 7)
#define SCULL_IOCQQSET _IO(SCULL_IOC_MAGIC, 8)
#define SCULL_IOCXQUANTUM _IOWR(SCULL_IOC_MAGIC, 9, int)
#define SCULL_IOCXQSET _IOWR(SCULL_IOC_MAGIC, 10, int)
#define SCULL_IOCHQUANTUM _IO(SCULL_IOC_MAGIC, 11)
#define SCULL_IOCHQSET _IO(SCULL_IOC_MAGIC, 12)

/*
 * The other entities only have "Tell" and "Query", because they're
 * not printed in the book, and there's no need to have all six.
 * (The previous stuff was only there to show different ways to do it.
 */
#define SCULL_P_IOCTSIZE _IO(SCULL_IOC_MAGIC, 13)
#define SCULL_P_IOCQSIZE _IO(SCULL_IOC_MAGIC, 14)
/* ... more to come */

#define SCULL_IOC_MAXNR 14

inode i;
pthread_mutex_t lock;

/* =====================================================
   Model for the Linux kernel API
   ===================================================== */
inline int down_interruptible() {
  pthread_mutex_lock(&lock);
  return 0; // lock is held
}

inline void up() {
  pthread_mutex_unlock(&lock);
  return;
}

#define container_of(dev) dev

inline unsigned_long copy_to_user(char to, char from, unsigned_long n) {
  to = from;
  return __VERIFIER_nondet_int();
}

inline unsigned_long copy_from_user(char to, char from, unsigned_long n) {
  to = from;
  return __VERIFIER_nondet_int();
}

inline int __get_user(int size, void_ptr ptr) {
  return __VERIFIER_nondet_int();
}

inline int __put_user(int size, void_ptr ptr) {
  return __VERIFIER_nondet_int();
}

/* =====================================================
   A model for the device-driver functions
   ===================================================== */
/*
 * scull.h -- definitions for the char module
 *
 * Copyright (C) 2001 Alessandro Rubini and Jonathan Corbet
 * Copyright (C) 2001 O'Reilly & Associates
 *
 * The source code in this file can be freely used, adapted,
 * and redistributed in source or binary form, so long as an
 * acknowledgment appears in derived source files.  The citation
 * should list that the code comes from the book "Linux Device
 * Drivers" by Alessandro Rubini and Jonathan Corbet, published
 * by O'Reilly & Associates.   No warranty is attached;
 * we cannot take responsibility for errors or fitness for use.
 *
 * $Id: scull.h,v 1.15 2004/11/04 17:51:18 rubini Exp $
 */

int scull_quantum = SCULL_QUANTUM;
int scull_qset = SCULL_QSET;
int dev_data;
int dev_quantum;
int dev_qset;
unsigned_long dev_size;
int __X__; // variable to test mutual exclusion

/*
 * Empty out the scull device; must be called with the device
 * semaphore held.
 */
int scull_trim(scull_dev dev) {
  int qset = dev_qset;

  dev_size = 0;
  dev_quantum = scull_quantum;
  dev_qset = scull_qset;
  dev_data = 0;
  return 0;
}

/*
 * Open and close
 */

inline int scull_open(int tid, inode i, file filp) {
  scull_dev dev;

  dev = container_of(i);
  filp = dev;

  if (down_interruptible())
    return -ERESTARTSYS;

  __X__ = 2;          /* check mutual exclusion */
  scull_trim(dev);    /* ignore errors */
  assert(__X__ >= 2); /* check mutual exclusion */
  up();
  return 0; /* success */
}

#define scull_release(i, filp) 0

/*
 * Follow the list
 */
inline scull_qset_type scull_follow(scull_dev dev, int n) {
  return __VERIFIER_nondet_int();
}

/*
 * Data management: read and write
 */

inline ssize_t scull_read(int tid, file filp, char buf, size_t count,
                          loff_t f_pos) {
  scull_dev dev = filp;
  scull_qset_type dptr; /* the first listitem */
  int quantum = dev_quantum, qset = dev_qset;
  int itemsize = quantum * qset; /* how many bytes in the listitem */
  int item, s_pos, q_pos, rest;
  ssize_t retval = 0;

  if (down_interruptible())
    return -ERESTARTSYS;

  __X__ = 0; /* check mutual exclusion */

  if (f_pos >= dev_size)
    goto out;
  if (f_pos + count >= dev_size)
    count = dev_size - f_pos;

  /* find listitem, qset index, and offset in the quantum */
  item = f_pos / itemsize;
  rest = f_pos;
  s_pos = rest / quantum;
  q_pos = rest;

  /* follow the list up to the right position (defined elsewhere) */
  dptr = scull_follow(dev, item);

  /* read only up to the end of this quantum */
  if (count > quantum - q_pos)
    count = quantum - q_pos;

  if (copy_to_user(buf, dev_data + s_pos + q_pos, count)) {
    retval = -EFAULT;
    goto out;
  }
  f_pos += count;
  retval = count;

  assert(__X__ <= 0); /* check mutual exclusion */

out:
  up();
  return retval;
}

inline ssize_t scull_write(int tid, file filp, char buf, size_t count,
                           loff_t f_pos) {
  scull_dev dev = filp;
  scull_qset_type dptr;
  int quantum = dev_quantum, qset = dev_qset;
  int itemsize = quantum * qset;
  int item, s_pos, q_pos, rest;
  ssize_t retval = -ENOMEM; /* value used in "goto out" statements */

  if (down_interruptible())
    return -ERESTARTSYS;

  /* find listitem, qset index and offset in the quantum */
  item = f_pos / itemsize;
  rest = f_pos;
  s_pos = rest / quantum;
  q_pos = rest;

  /* follow the list up to the right position */
  dptr = scull_follow(dev, item);
  if (dptr == 0)
    goto out;

  /* write only up to the end of this quantum */
  if (count > quantum - q_pos)
    count = quantum - q_pos;

  __X__ = 1; /* check mutual exclusion */

  if (copy_from_user(dev_data + s_pos + q_pos, buf, count)) {
    retval = -EFAULT;
    goto out;
  }
  f_pos += count;
  retval = count;

  /* update the size */
  if (dev_size < f_pos)
    dev_size = f_pos;

  assert(__X__ == 1); /* check mutual exclusion */

out:
  up();
  return retval;
}

/*
 * The ioctl() implementation
 */

inline int scull_ioctl(inode i, file filp, unsigned_int cmd,
                       unsigned_long arg) {

  int err = 0, tmp;
  int retval = 0;

  switch (cmd) {

  case SCULL_IOCRESET:
    scull_quantum = SCULL_QUANTUM;
    scull_qset = SCULL_QSET;
    break;

  case SCULL_IOCSQUANTUM: /* Set: arg points to the value */
    retval = __get_user(scull_quantum, arg);
    break;

  case SCULL_IOCTQUANTUM: /* Tell: arg is the value */
    scull_quantum = arg;
    break;

  case SCULL_IOCGQUANTUM: /* Get: arg is pointer to result */
    retval = __put_user(scull_quantum, arg);
    break;

  case SCULL_IOCQQUANTUM: /* Query: return it (it's positive) */
    return scull_quantum;

  case SCULL_IOCXQUANTUM: /* eXchange: use arg as pointer */
    tmp = scull_quantum;
    retval = __get_user(scull_quantum, arg);
    if (retval == 0)
      retval = __put_user(tmp, arg);
    break;

  case SCULL_IOCHQUANTUM: /* sHift: like Tell + Query */
    tmp = scull_quantum;
    scull_quantum = arg;
    return tmp;

  case SCULL_IOCSQSET:
    retval = __get_user(scull_qset, arg);
    break;

  case SCULL_IOCTQSET:
    scull_qset = arg;
    break;

  case SCULL_IOCGQSET:
    retval = __put_user(scull_qset, arg);
    break;

  case SCULL_IOCQQSET:
    return scull_qset;

  case SCULL_IOCXQSET:
    tmp = scull_qset;
    retval = __get_user(scull_qset, arg);
    if (retval == 0)
      retval = __put_user(tmp, arg);
    break;

  case SCULL_IOCHQSET:
    tmp = scull_qset;
    scull_qset = arg;
    return tmp;

  default: /* redundant, as cmd was checked against MAXNR */
    return -ENOTTY;
  }
  return retval;
}

/*
 * The "extended" operations -- only seek
 */

inline loff_t scull_llseek(file filp, loff_t off, int whence, loff_t f_pos) {
  scull_dev dev = filp;
  loff_t newpos;

  switch (whence) {
  case 0: /* SEEK_SET */
    newpos = off;
    break;

  case 1: /* SEEK_CUR */
    newpos = filp + f_pos + off;
    break;

  case 2: /* SEEK_END */
    newpos = dev_size + off;
    break;

  default: /* can't happen */
    return -EINVAL;
  }
  if (newpos < 0)
    return -EINVAL;
  filp = newpos;
  return newpos;
}

/*
 * Finally, the module stuff
 */

/*
 * The cleanup function is used to handle initialization failures as well.
 * Thefore, it must be careful to work correctly even if some of the items
 * have not been initialized
 */
inline void scull_cleanup_module(void) {
  scull_dev dev;
  scull_trim(dev);
}

inline int scull_init_module() {
  int result = 0;
  return 0;

fail:
  scull_cleanup_module();
  return result;
}

/* =====================================================
   User program calling functions from the device driver
   ===================================================== */
void *loader(void *arg) {
  scull_init_module();
  scull_cleanup_module();
}

void *thread1(void *arg) {
  file filp;
  char buf;
  size_t count = 10;
  loff_t off = 0;
  scull_open(tid1, i, filp);
  scull_read(tid1, filp, buf, count, off);
  scull_release(i, filp);
}

void *thread2(void *arg) {
  file filp;
  char buf;
  size_t count = 10;
  loff_t off = 0;
  scull_open(tid2, i, filp);
  scull_write(tid2, filp, buf, count, off);
  scull_release(i, filp);
}

int main() {
  pthread_t t1, t2, t3;
  pthread_mutex_init(&lock, FILE_WITH_LOCK_UNLOCKED);
  pthread_create(&t1, 0, loader, 0);
  pthread_create(&t2, 0, thread1, 0);
  pthread_create(&t3, 0, thread2, 0);
  pthread_join(t1, 0);
  pthread_join(t2, 0);
  pthread_join(t3, 0);
  pthread_mutex_destroy(&lock);
  return 0;
}
