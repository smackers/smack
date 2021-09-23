//
// This file is distributed under the MIT License. See LICENSE for details.
//
#include <limits.h>
#include <smack.h>
#include <stddef.h>
#include <stdlib.h>
#include <string.h>

/**
 * The SMACK "prelude" definitions
 *
 * TODO add more documentation
 *
 * NOTES ON MEMORY MODELS
 *
 * 1. addresses are (unbounded) integers
 * 2. one unbounded integer is stored at each address
 * 3. (NO-REUSE only) heap addresses are allocated in a strictly increasing
 *    fashion
 * 4. (NO-REUSE only) freed (heap) addresses are never reallocated
 * 5. the address space is partitioned as follows
 *
 * Address A                                        Allocation
 * ---------                                        ----------
 * A > 0                                            Heap
 * A = 0                                            Not allocated (null)
 * $GLOBALS_BOTTOM <= A < 0                         Static (global storage)
 * $GLOBALS_BOTTOM - 32768 <= A < $GLOBALS_BOTTOM   Not allocated (padding)
 * $EXTERNS_BOTTOM <= A < $GLOBALS_BOTTOM - 32768   External globals
 * A < $EXTERNS_BOTTOM                              Objects returned from
 * external functions
 *
 */

void *__builtinx_va_arg(char *x) {
  __SMACK_code("assume false;");
  return 0;
}

long __builtinx_expect(long exp, long c) { return exp; }

void __VERIFIER_assume(int x) {
  __SMACK_dummy(x);
  __SMACK_code("assume @ != $0;", x);
}

#ifndef SVCOMP
void __VERIFIER_assert(int x) {
#if !DISABLE_SMACK_ASSERTIONS
  __SMACK_dummy(x);
  __SMACK_code("assert @ != $0;", x);
#endif
}
#endif

int __SMACK_and32(int a, int b) {
  int c = 0;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 2147483647) {
      c += 1;
    }
  }
  a = a % 2147483648;
  a += a;
  b = b % 2147483648;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 2147483647) {
      c += 1;
    }
  }
  a = a % 2147483648;
  a += a;
  b = b % 2147483648;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 2147483647) {
      c += 1;
    }
  }
  a = a % 2147483648;
  a += a;
  b = b % 2147483648;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 2147483647) {
      c += 1;
    }
  }
  a = a % 2147483648;
  a += a;
  b = b % 2147483648;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 2147483647) {
      c += 1;
    }
  }
  a = a % 2147483648;
  a += a;
  b = b % 2147483648;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 2147483647) {
      c += 1;
    }
  }
  a = a % 2147483648;
  a += a;
  b = b % 2147483648;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 2147483647) {
      c += 1;
    }
  }
  a = a % 2147483648;
  a += a;
  b = b % 2147483648;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 2147483647) {
      c += 1;
    }
  }
  a = a % 2147483648;
  a += a;
  b = b % 2147483648;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 2147483647) {
      c += 1;
    }
  }
  a = a % 2147483648;
  a += a;
  b = b % 2147483648;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 2147483647) {
      c += 1;
    }
  }
  a = a % 2147483648;
  a += a;
  b = b % 2147483648;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 2147483647) {
      c += 1;
    }
  }
  a = a % 2147483648;
  a += a;
  b = b % 2147483648;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 2147483647) {
      c += 1;
    }
  }
  a = a % 2147483648;
  a += a;
  b = b % 2147483648;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 2147483647) {
      c += 1;
    }
  }
  a = a % 2147483648;
  a += a;
  b = b % 2147483648;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 2147483647) {
      c += 1;
    }
  }
  a = a % 2147483648;
  a += a;
  b = b % 2147483648;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 2147483647) {
      c += 1;
    }
  }
  a = a % 2147483648;
  a += a;
  b = b % 2147483648;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 2147483647) {
      c += 1;
    }
  }
  a = a % 2147483648;
  a += a;
  b = b % 2147483648;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 2147483647) {
      c += 1;
    }
  }
  a = a % 2147483648;
  a += a;
  b = b % 2147483648;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 2147483647) {
      c += 1;
    }
  }
  a = a % 2147483648;
  a += a;
  b = b % 2147483648;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 2147483647) {
      c += 1;
    }
  }
  a = a % 2147483648;
  a += a;
  b = b % 2147483648;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 2147483647) {
      c += 1;
    }
  }
  a = a % 2147483648;
  a += a;
  b = b % 2147483648;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 2147483647) {
      c += 1;
    }
  }
  a = a % 2147483648;
  a += a;
  b = b % 2147483648;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 2147483647) {
      c += 1;
    }
  }
  a = a % 2147483648;
  a += a;
  b = b % 2147483648;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 2147483647) {
      c += 1;
    }
  }
  a = a % 2147483648;
  a += a;
  b = b % 2147483648;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 2147483647) {
      c += 1;
    }
  }
  a = a % 2147483648;
  a += a;
  b = b % 2147483648;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 2147483647) {
      c += 1;
    }
  }
  a = a % 2147483648;
  a += a;
  b = b % 2147483648;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 2147483647) {
      c += 1;
    }
  }
  a = a % 2147483648;
  a += a;
  b = b % 2147483648;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 2147483647) {
      c += 1;
    }
  }
  a = a % 2147483648;
  a += a;
  b = b % 2147483648;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 2147483647) {
      c += 1;
    }
  }
  a = a % 2147483648;
  a += a;
  b = b % 2147483648;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 2147483647) {
      c += 1;
    }
  }
  a = a % 2147483648;
  a += a;
  b = b % 2147483648;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 2147483647) {
      c += 1;
    }
  }
  a = a % 2147483648;
  a += a;
  b = b % 2147483648;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 2147483647) {
      c += 1;
    }
  }
  a = a % 2147483648;
  a += a;
  b = b % 2147483648;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 2147483647) {
      c += 1;
    }
  }
  a = a % 2147483648;
  a += a;
  b = b % 2147483648;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 2147483647) {
      c += 1;
    }
  }
  a = a % 2147483648;
  a += a;
  b = b % 2147483648;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 2147483647) {
      c += 1;
    }
  }
  a = a % 2147483648;
  a += a;
  b = b % 2147483648;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 2147483647) {
      c += 1;
    }
  }
  a = a % 2147483648;
  a += a;
  b = b % 2147483648;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 2147483647) {
      c += 1;
    }
  }
  a = a % 2147483648;
  a += a;
  b = b % 2147483648;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 2147483647) {
      c += 1;
    }
  }
  a = a % 2147483648;
  a += a;
  b = b % 2147483648;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 2147483647) {
      c += 1;
    }
  }
  a = a % 2147483648;
  a += a;
  b = b % 2147483648;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 2147483647) {
      c += 1;
    }
  }
  a = a % 2147483648;
  a += a;
  b = b % 2147483648;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 2147483647) {
      c += 1;
    }
  }
  a = a % 2147483648;
  a += a;
  b = b % 2147483648;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 2147483647) {
      c += 1;
    }
  }
  a = a % 2147483648;
  a += a;
  b = b % 2147483648;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 2147483647) {
      c += 1;
    }
  }
  a = a % 2147483648;
  a += a;
  b = b % 2147483648;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 2147483647) {
      c += 1;
    }
  }
  a = a % 2147483648;
  a += a;
  b = b % 2147483648;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 2147483647) {
      c += 1;
    }
  }
  a = a % 2147483648;
  a += a;
  b = b % 2147483648;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 2147483647) {
      c += 1;
    }
  }
  a = a % 2147483648;
  a += a;
  b = b % 2147483648;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 2147483647) {
      c += 1;
    }
  }
  a = a % 2147483648;
  a += a;
  b = b % 2147483648;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 2147483647) {
      c += 1;
    }
  }
  a = a % 2147483648;
  a += a;
  b = b % 2147483648;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 2147483647) {
      c += 1;
    }
  }
  a = a % 2147483648;
  a += a;
  b = b % 2147483648;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 2147483647) {
      c += 1;
    }
  }
  a = a % 2147483648;
  a += a;
  b = b % 2147483648;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 2147483647) {
      c += 1;
    }
  }
  a = a % 2147483648;
  a += a;
  b = b % 2147483648;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 2147483647) {
      c += 1;
    }
  }
  a = a % 2147483648;
  a += a;
  b = b % 2147483648;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 2147483647) {
      c += 1;
    }
  }
  a = a % 2147483648;
  a += a;
  b = b % 2147483648;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 2147483647) {
      c += 1;
    }
  }
  a = a % 2147483648;
  a += a;
  b = b % 2147483648;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 2147483647) {
      c += 1;
    }
  }
  a = a % 2147483648;
  a += a;
  b = b % 2147483648;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 2147483647) {
      c += 1;
    }
  }
  a = a % 2147483648;
  a += a;
  b = b % 2147483648;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 2147483647) {
      c += 1;
    }
  }
  a = a % 2147483648;
  a += a;
  b = b % 2147483648;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 2147483647) {
      c += 1;
    }
  }
  a = a % 2147483648;
  a += a;
  b = b % 2147483648;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 2147483647) {
      c += 1;
    }
  }
  a = a % 2147483648;
  a += a;
  b = b % 2147483648;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 2147483647) {
      c += 1;
    }
  }
  a = a % 2147483648;
  a += a;
  b = b % 2147483648;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 2147483647) {
      c += 1;
    }
  }
  a = a % 2147483648;
  a += a;
  b = b % 2147483648;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 2147483647) {
      c += 1;
    }
  }
  a = a % 2147483648;
  a += a;
  b = b % 2147483648;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 2147483647) {
      c += 1;
    }
  }
  a = a % 2147483648;
  a += a;
  b = b % 2147483648;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 2147483647) {
      c += 1;
    }
  }
  a = a % 2147483648;
  a += a;
  b = b % 2147483648;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 2147483647) {
      c += 1;
    }
  }
  a = a % 2147483648;
  a += a;
  b = b % 2147483648;
  b += b;

  return c;
}

long __SMACK_and64(long a, long b) { return (long)__SMACK_and32(a, b); }

short __SMACK_and16(short a, short b) {
  short c = 0;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 32767) {
      c += 1;
    }
  }
  a = a % 32768;
  a += a;
  b = b % 32768;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 32767) {
      c += 1;
    }
  }
  a = a % 32768;
  a += a;
  b = b % 32768;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 32767) {
      c += 1;
    }
  }
  a = a % 32768;
  a += a;
  b = b % 32768;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 32767) {
      c += 1;
    }
  }
  a = a % 32768;
  a += a;
  b = b % 32768;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 32767) {
      c += 1;
    }
  }
  a = a % 32768;
  a += a;
  b = b % 32768;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 32767) {
      c += 1;
    }
  }
  a = a % 32768;
  a += a;
  b = b % 32768;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 32767) {
      c += 1;
    }
  }
  a = a % 32768;
  a += a;
  b = b % 32768;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 32767) {
      c += 1;
    }
  }
  a = a % 32768;
  a += a;
  b = b % 32768;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 32767) {
      c += 1;
    }
  }
  a = a % 32768;
  a += a;
  b = b % 32768;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 32767) {
      c += 1;
    }
  }
  a = a % 32768;
  a += a;
  b = b % 32768;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 32767) {
      c += 1;
    }
  }
  a = a % 32768;
  a += a;
  b = b % 32768;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 32767) {
      c += 1;
    }
  }
  a = a % 32768;
  a += a;
  b = b % 32768;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 32767) {
      c += 1;
    }
  }
  a = a % 32768;
  a += a;
  b = b % 32768;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 32767) {
      c += 1;
    }
  }
  a = a % 32768;
  a += a;
  b = b % 32768;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 32767) {
      c += 1;
    }
  }
  a = a % 32768;
  a += a;
  b = b % 32768;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 32767) {
      c += 1;
    }
  }
  a = a % 32768;
  a += a;
  b = b % 32768;
  b += b;

  return c;
}

char __SMACK_and8(char a, char b) {
  char c = 0;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 127) {
      c += 1;
    }
  }
  a = a % 128;
  a += a;
  b = b % 128;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 127) {
      c += 1;
    }
  }
  a = a % 128;
  a += a;
  b = b % 128;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 127) {
      c += 1;
    }
  }
  a = a % 128;
  a += a;
  b = b % 128;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 127) {
      c += 1;
    }
  }
  a = a % 128;
  a += a;
  b = b % 128;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 127) {
      c += 1;
    }
  }
  a = a % 128;
  a += a;
  b = b % 128;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 127) {
      c += 1;
    }
  }
  a = a % 128;
  a += a;
  b = b % 128;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 127) {
      c += 1;
    }
  }
  a = a % 128;
  a += a;
  b = b % 128;
  b += b;

  c += c;
  if (a < 0) {
    if (b < 0 || b > 127) {
      c += 1;
    }
  }
  a = a % 128;
  a += a;
  b = b % 128;
  b += b;

  return c;
}

int __SMACK_or32(int a, int b) {
  int c = 0;

  c += c;
  if (a < 0) {
    c += 1;
  } else if (b < 0) {
    c += 1;
  }
  a += a;
  a = a % 2147483648;
  b += b;
  b = b % 2147483648;

  c += c;
  if (a < 0) {
    c += 1;
  } else if (b < 0) {
    c += 1;
  }
  a += a;
  a = a % 2147483648;
  b += b;
  b = b % 2147483648;

  c += c;
  if (a < 0) {
    c += 1;
  } else if (b < 0) {
    c += 1;
  }
  a += a;
  a = a % 2147483648;
  b += b;
  b = b % 2147483648;

  c += c;
  if (a < 0) {
    c += 1;
  } else if (b < 0) {
    c += 1;
  }
  a += a;
  a = a % 2147483648;
  b += b;
  b = b % 2147483648;

  c += c;
  if (a < 0) {
    c += 1;
  } else if (b < 0) {
    c += 1;
  }
  a += a;
  a = a % 2147483648;
  b += b;
  b = b % 2147483648;

  c += c;
  if (a < 0) {
    c += 1;
  } else if (b < 0) {
    c += 1;
  }
  a += a;
  a = a % 2147483648;
  b += b;
  b = b % 2147483648;

  c += c;
  if (a < 0) {
    c += 1;
  } else if (b < 0) {
    c += 1;
  }
  a += a;
  a = a % 2147483648;
  b += b;
  b = b % 2147483648;

  c += c;
  if (a < 0) {
    c += 1;
  } else if (b < 0) {
    c += 1;
  }
  a += a;
  a = a % 2147483648;
  b += b;
  b = b % 2147483648;

  c += c;
  if (a < 0) {
    c += 1;
  } else if (b < 0) {
    c += 1;
  }
  a += a;
  a = a % 2147483648;
  b += b;
  b = b % 2147483648;

  c += c;
  if (a < 0) {
    c += 1;
  } else if (b < 0) {
    c += 1;
  }
  a += a;
  a = a % 2147483648;
  b += b;
  b = b % 2147483648;

  c += c;
  if (a < 0) {
    c += 1;
  } else if (b < 0) {
    c += 1;
  }
  a += a;
  a = a % 2147483648;
  b += b;
  b = b % 2147483648;

  c += c;
  if (a < 0) {
    c += 1;
  } else if (b < 0) {
    c += 1;
  }
  a += a;
  a = a % 2147483648;
  b += b;
  b = b % 2147483648;

  c += c;
  if (a < 0) {
    c += 1;
  } else if (b < 0) {
    c += 1;
  }
  a += a;
  a = a % 2147483648;
  b += b;
  b = b % 2147483648;

  c += c;
  if (a < 0) {
    c += 1;
  } else if (b < 0) {
    c += 1;
  }
  a += a;
  a = a % 2147483648;
  b += b;
  b = b % 2147483648;

  c += c;
  if (a < 0) {
    c += 1;
  } else if (b < 0) {
    c += 1;
  }
  a += a;
  a = a % 2147483648;
  b += b;
  b = b % 2147483648;

  c += c;
  if (a < 0) {
    c += 1;
  } else if (b < 0) {
    c += 1;
  }
  a += a;
  a = a % 2147483648;
  b += b;
  b = b % 2147483648;

  c += c;
  if (a < 0) {
    c += 1;
  } else if (b < 0) {
    c += 1;
  }
  a += a;
  a = a % 2147483648;
  b += b;
  b = b % 2147483648;

  c += c;
  if (a < 0) {
    c += 1;
  } else if (b < 0) {
    c += 1;
  }
  a += a;
  a = a % 2147483648;
  b += b;
  b = b % 2147483648;

  c += c;
  if (a < 0) {
    c += 1;
  } else if (b < 0) {
    c += 1;
  }
  a += a;
  a = a % 2147483648;
  b += b;
  b = b % 2147483648;

  c += c;
  if (a < 0) {
    c += 1;
  } else if (b < 0) {
    c += 1;
  }
  a += a;
  a = a % 2147483648;
  b += b;
  b = b % 2147483648;

  c += c;
  if (a < 0) {
    c += 1;
  } else if (b < 0) {
    c += 1;
  }
  a += a;
  a = a % 2147483648;
  b += b;
  b = b % 2147483648;

  c += c;
  if (a < 0) {
    c += 1;
  } else if (b < 0) {
    c += 1;
  }
  a += a;
  a = a % 2147483648;
  b += b;
  b = b % 2147483648;

  c += c;
  if (a < 0) {
    c += 1;
  } else if (b < 0) {
    c += 1;
  }
  a += a;
  a = a % 2147483648;
  b += b;
  b = b % 2147483648;

  c += c;
  if (a < 0) {
    c += 1;
  } else if (b < 0) {
    c += 1;
  }
  a += a;
  a = a % 2147483648;
  b += b;
  b = b % 2147483648;

  c += c;
  if (a < 0) {
    c += 1;
  } else if (b < 0) {
    c += 1;
  }
  a += a;
  a = a % 2147483648;
  b += b;
  b = b % 2147483648;

  c += c;
  if (a < 0) {
    c += 1;
  } else if (b < 0) {
    c += 1;
  }
  a += a;
  a = a % 2147483648;
  b += b;
  b = b % 2147483648;

  c += c;
  if (a < 0) {
    c += 1;
  } else if (b < 0) {
    c += 1;
  }
  a += a;
  a = a % 2147483648;
  b += b;
  b = b % 2147483648;

  c += c;
  if (a < 0) {
    c += 1;
  } else if (b < 0) {
    c += 1;
  }
  a += a;
  a = a % 2147483648;
  b += b;
  b = b % 2147483648;

  c += c;
  if (a < 0) {
    c += 1;
  } else if (b < 0) {
    c += 1;
  }
  a += a;
  a = a % 2147483648;
  b += b;
  b = b % 2147483648;

  c += c;
  if (a < 0) {
    c += 1;
  } else if (b < 0) {
    c += 1;
  }
  a += a;
  a = a % 2147483648;
  b += b;
  b = b % 2147483648;

  c += c;
  if (a < 0) {
    c += 1;
  } else if (b < 0) {
    c += 1;
  }
  a += a;
  a = a % 2147483648;
  b += b;
  b = b % 2147483648;

  c += c;
  if (a < 0) {
    c += 1;
  } else if (b < 0) {
    c += 1;
  }
  a += a;
  a = a % 2147483648;
  b += b;
  b = b % 2147483648;

  return c;
}

long __SMACK_or64(long a, long b) { return (long)__SMACK_or32(a, b); }
short __SMACK_or16(short a, short b) { return (short)__SMACK_or32(a, b); }
char __SMACK_or8(char a, char b) { return (char)__SMACK_or32(a, b); }

void __SMACK_check_overflow(int flag) {
  __SMACK_dummy(flag);
  __SMACK_code("assert {:overflow} @ == $0;", flag);
}

void __SMACK_loop_exit(void) { __SMACK_code("assert {:loopexit} false;"); }

char __VERIFIER_nondet_char(void) {
  char x = __SMACK_nondet_char();
  __VERIFIER_assume(x >= SCHAR_MIN && x <= SCHAR_MAX);
  return x;
}

signed char __VERIFIER_nondet_signed_char(void) {
  signed char x = __SMACK_nondet_signed_char();
  __VERIFIER_assume(x >= SCHAR_MIN && x <= SCHAR_MAX);
  return x;
}

unsigned char __VERIFIER_nondet_unsigned_char(void) {
  unsigned char x = __SMACK_nondet_unsigned_char();
  __VERIFIER_assume(x >= 0 && x <= UCHAR_MAX);
  return x;
}

short __VERIFIER_nondet_short(void) {
  short x = __SMACK_nondet_short();
  __VERIFIER_assume(x >= SHRT_MIN && x <= SHRT_MAX);
  return x;
}

signed short __VERIFIER_nondet_signed_short(void) {
  signed short x = __SMACK_nondet_signed_short();
  __VERIFIER_assume(x >= SHRT_MIN && x <= SHRT_MAX);
  return x;
}

signed short int __VERIFIER_nondet_signed_short_int(void) {
  signed short int x = __SMACK_nondet_signed_short_int();
  __VERIFIER_assume(x >= SHRT_MIN && x <= SHRT_MAX);
  return x;
}

unsigned short __VERIFIER_nondet_unsigned_short(void) {
  unsigned short x = __SMACK_nondet_unsigned_short();
  __VERIFIER_assume(x >= 0 && x <= USHRT_MAX);
  return x;
}

unsigned short int __VERIFIER_nondet_unsigned_short_int(void) {
  unsigned short int x = __SMACK_nondet_unsigned_short_int();
  __VERIFIER_assume(x >= 0 && x <= USHRT_MAX);
  return x;
}

int __VERIFIER_nondet_int(void) {
  int x = __SMACK_nondet_int();
  __VERIFIER_assume(x >= INT_MIN && x <= INT_MAX);
  return x;
}

signed int __VERIFIER_nondet_signed_int(void) {
  signed int x = __SMACK_nondet_signed_int();
  __VERIFIER_assume(x >= INT_MIN && x <= INT_MAX);
  return x;
}

unsigned __VERIFIER_nondet_unsigned(void) {
  unsigned x = __SMACK_nondet_unsigned();
  unsigned min = __SMACK_nondet_unsigned();
  unsigned max = __SMACK_nondet_unsigned();
  __VERIFIER_assume(min == 0 && max >= UINT_MAX && max <= UINT_MAX);
  __VERIFIER_assume(x >= min && x <= max);
  return x;
}

unsigned int __VERIFIER_nondet_unsigned_int(void) {
  unsigned int x = __SMACK_nondet_unsigned_int();
  unsigned int min = __SMACK_nondet_unsigned_int();
  unsigned int max = __SMACK_nondet_unsigned_int();
  __VERIFIER_assume(min == 0 && max >= UINT_MAX && max <= UINT_MAX);
  __VERIFIER_assume(x >= min && x <= max);
  return x;
}

long __VERIFIER_nondet_long(void) {
  long x = __SMACK_nondet_long();
  __VERIFIER_assume(x >= LONG_MIN && x <= LONG_MAX);
  return x;
}

long int __VERIFIER_nondet_long_int(void) {
  long int x = __SMACK_nondet_long_int();
  __VERIFIER_assume(x >= LONG_MIN && x <= LONG_MAX);
  return x;
}

signed long __VERIFIER_nondet_signed_long(void) {
  signed long x = __SMACK_nondet_signed_long();
  __VERIFIER_assume(x >= LONG_MIN && x <= LONG_MAX);
  return x;
}

signed long int __VERIFIER_nondet_signed_long_int(void) {
  signed long int x = __SMACK_nondet_signed_long_int();
  __VERIFIER_assume(x >= LONG_MIN && x <= LONG_MAX);
  return x;
}

unsigned long __VERIFIER_nondet_unsigned_long(void) {
  unsigned long x = __SMACK_nondet_unsigned_long();
  unsigned long min = __SMACK_nondet_unsigned_long();
  unsigned long max = __SMACK_nondet_unsigned_long();
  __VERIFIER_assume(min == 0 && max >= ULONG_MAX && max <= ULONG_MAX);
  __VERIFIER_assume(x >= min && x <= max);
  return x;
}

unsigned long int __VERIFIER_nondet_unsigned_long_int(void) {
  unsigned long int x = __SMACK_nondet_unsigned_long_int();
  unsigned long int min = __SMACK_nondet_unsigned_long_int();
  unsigned long int max = __SMACK_nondet_unsigned_long_int();
  __VERIFIER_assume(min == 0 && max >= ULONG_MAX && max <= ULONG_MAX);
  __VERIFIER_assume(x >= min && x <= max);
  return x;
}

long long __VERIFIER_nondet_long_long(void) {
  long long x = __SMACK_nondet_long_long();
  __VERIFIER_assume(x >= LLONG_MIN && x <= LLONG_MAX);
  return x;
}

long long int __VERIFIER_nondet_long_long_int(void) {
  long long int x = __SMACK_nondet_long_long_int();
  __VERIFIER_assume(x >= LLONG_MIN && x <= LLONG_MAX);
  return x;
}

signed long long __VERIFIER_nondet_signed_long_long(void) {
  signed long long x = __SMACK_nondet_signed_long_long();
  __VERIFIER_assume(x >= LLONG_MIN && x <= LLONG_MAX);
  return x;
}

signed long long int __VERIFIER_nondet_signed_long_long_int(void) {
  signed long long int x = __SMACK_nondet_signed_long_long_int();
  __VERIFIER_assume(x >= LLONG_MIN && x <= LLONG_MAX);
  return x;
}

unsigned long long __VERIFIER_nondet_unsigned_long_long(void) {
  unsigned long long x = __SMACK_nondet_unsigned_long_long();
  unsigned long long min = __SMACK_nondet_unsigned_long_long();
  unsigned long long max = __SMACK_nondet_unsigned_long_long();
  __VERIFIER_assume(min == 0 && max >= ULLONG_MAX && max <= ULLONG_MAX);
  __VERIFIER_assume(x >= min && x <= max);
  return x;
}

unsigned long long int __VERIFIER_nondet_unsigned_long_long_int(void) {
  unsigned long long int x = __SMACK_nondet_unsigned_long_long_int();
  unsigned long long int min = __SMACK_nondet_unsigned_long_long_int();
  unsigned long long int max = __SMACK_nondet_unsigned_long_long_int();
  __VERIFIER_assume(min == 0 && max >= ULLONG_MAX && max <= ULLONG_MAX);
  __VERIFIER_assume(x >= min && x <= max);
  return x;
}

// Used in SVCCOMP benchmarks

_Bool __VERIFIER_nondet_bool(void) {
  _Bool x = (_Bool)__VERIFIER_nondet_int();
  __VERIFIER_assume(x == 0 || x == 1);
  return x;
}

unsigned char __VERIFIER_nondet_uchar(void) {
  unsigned char x = __VERIFIER_nondet_unsigned_char();
  return x;
}

unsigned short __VERIFIER_nondet_ushort(void) {
  unsigned short x = __VERIFIER_nondet_unsigned_short();
  return x;
}

unsigned int __VERIFIER_nondet_uint(void) {
  unsigned int x = __VERIFIER_nondet_unsigned_int();
  return x;
}

unsigned long __VERIFIER_nondet_ulong(void) {
  unsigned long x = __VERIFIER_nondet_unsigned_long();
  return x;
}

void *__VERIFIER_nondet_pointer(void) { return __VERIFIER_nondet(); }

void __SMACK_dummy(int v) { __SMACK_code("assume true;"); }

#define D(d) __SMACK_top_decl(d)

void __SMACK_decls(void) {
  // Memory debugging symbols
  D("type $mop;");
  D("procedure boogie_si_record_mop(m: $mop);");
  D("const $MOP: $mop;");

  D("var $exn: bool;");
  D("var $exnv: int;");

  // Concurrency primitives
  D("procedure corral_atomic_begin();");
  D("procedure corral_atomic_end();");

  D("procedure $alloc(n: ref) returns (p: ref)\n"
    "{\n"
    "  call corral_atomic_begin();\n"
    "  call p := $$alloc(n);\n"
    "  call corral_atomic_end();\n"
    "}\n");

#if MEMORY_SAFETY
  __SMACK_dummy((int)__SMACK_check_memory_safety);
  D("implementation __SMACK_check_memory_safety(p: ref, size: ref)\n"
    "{\n"
    "  assert {:valid_deref} $Alloc[$base(p)];\n"
    "  assert {:valid_deref} $sle.ref.bool($base(p), p);\n"
#if MEMORY_MODEL_NO_REUSE_IMPLS
    "  assert {:valid_deref} $sle.ref.bool($add.ref(p, size), "
    "$add.ref($base(p), $Size($base(p))));\n"
#elif MEMORY_MODEL_REUSE
    "  assert {:valid_deref} $sle.ref.bool($add.ref(p, size), "
    "$add.ref($base(p), $Size[$base(p)]));\n"
#else
    "  assert {:valid_deref} $sle.ref.bool($add.ref(p, size), "
    "$add.ref($base(p), $Size($base(p))));\n"
#endif
    "}\n");

  D("function $base(ref) returns (ref);");
  D("var $allocatedCounter: int;\n");

  D("procedure $malloc(n: ref) returns (p: ref)\n"
    "modifies $allocatedCounter;\n"
    "{\n"
    "  call corral_atomic_begin();\n"
    "  if ($ne.ref.bool(n, $0.ref)) {\n"
    "    $allocatedCounter := $allocatedCounter + 1;\n"
    "  }\n"
    "  call p := $$alloc(n);\n"
    "  call corral_atomic_end();\n"
    "}\n");

#if MEMORY_MODEL_NO_REUSE_IMPLS
  D("var $Alloc: [ref] bool;");
  D("function $Size(ref) returns (ref);");
  D("var $CurrAddr:ref;\n");

  // LLVM does not allocated globals explicitly. Hence, we do it in our prelude
  // before the program starts using the $galloc procedure.
  D("procedure $galloc(base_addr: ref, size: ref)\n"
    "{\n"
    "  assume $Size(base_addr) == size;\n"
    "  assume (forall addr: ref :: {$base(addr)} $sle.ref.bool(base_addr, "
    "addr) && $slt.ref.bool(addr, $add.ref(base_addr, size)) ==> $base(addr) "
    "== base_addr);\n"
    "  $Alloc[base_addr] := true;\n"
    "}\n");

  D("procedure {:inline 1} $$alloc(n: ref) returns (p: ref)\n"
    "modifies $Alloc, $CurrAddr;\n"
    "{\n"
    "  assume $sle.ref.bool($0.ref, n);\n"
    "  if ($slt.ref.bool($0.ref, n)) {\n"
    "    p := $CurrAddr;\n"
    "    havoc $CurrAddr;\n"
    "    assume $sge.ref.bool($sub.ref($CurrAddr, n), p);\n"
    "    assume $sgt.ref.bool($CurrAddr, $0.ref) && $slt.ref.bool($CurrAddr, "
    "$MALLOC_TOP);\n"
    "    assume $Size(p) == n;\n"
    "    assume (forall q: ref :: {$base(q)} $sle.ref.bool(p, q) && "
    "$slt.ref.bool(q, $add.ref(p, n)) ==> $base(q) == p);\n"
    "    $Alloc[p] := true;\n"
    "  }\n"
    "}\n");

  D("procedure $free(p: ref)\n"
    "modifies $Alloc, $allocatedCounter;\n"
    "{\n"
    "  call corral_atomic_begin();\n"
    "  if ($ne.ref.bool(p, $0.ref)) {\n"
    "    assert {:valid_free} $eq.ref.bool($base(p), p);\n"
    "    assert {:valid_free} $Alloc[p];\n"
    "    assert {:valid_free} $slt.ref.bool($0.ref, p);\n"
    "    $Alloc[p] := false;\n"
    "    $allocatedCounter := $allocatedCounter - 1;\n"
    "  }\n"
    "  call corral_atomic_end();\n"
    "}\n");

#elif MEMORY_MODEL_REUSE // can reuse previously-allocated and freed addresses
  D("var $Alloc: [ref] bool;");
  D("var $Size: [ref] ref;\n");

  // LLVM does not allocated globals explicitly. Hence, we do it in our prelude
  // before the program starts using the $galloc procedure.
  D("procedure $galloc(base_addr: ref, size: ref);\n"
    "modifies $Alloc, $Size;\n"
    "ensures $Size[base_addr] == size;\n"
    "ensures (forall addr: ref :: {$base(addr)} $sle.ref.bool(base_addr, addr) "
    "&& $slt.ref.bool(addr, $add.ref(base_addr, size)) ==> $base(addr) == "
    "base_addr);\n"
    "ensures $Alloc[base_addr];\n"
    "ensures (forall q: ref :: {$Size[q]} q != base_addr ==> $Size[q] == "
    "old($Size[q]));\n"
    "ensures (forall q: ref :: {$Alloc[q]} q != base_addr ==> $Alloc[q] == "
    "old($Alloc[q]));\n");

  D("procedure {:inline 1} $$alloc(n: ref) returns (p: ref);\n"
    "modifies $Alloc, $Size;\n"
    "ensures $sle.ref.bool($0.ref, n);\n"
    "ensures $slt.ref.bool($0.ref, n) ==> $slt.ref.bool($0.ref, p) && "
    "$slt.ref.bool(p, $sub.ref($MALLOC_TOP, n));\n"
    "ensures $eq.ref.bool(n, $0.ref) ==> p == $0.ref;\n"
    "ensures !old($Alloc[p]);\n"
    "ensures (forall q: ref :: old($Alloc[q]) ==> ($slt.ref.bool($add.ref(p, "
    "n), q) || $slt.ref.bool($add.ref(q, $Size[q]), p)));\n"
    "ensures $Alloc[p];\n"
    "ensures $Size[p] == n;\n"
    "ensures (forall q: ref :: {$Size[q]} q != p ==> $Size[q] == "
    "old($Size[q]));\n"
    "ensures (forall q: ref :: {$Alloc[q]} q != p ==> $Alloc[q] == "
    "old($Alloc[q]));\n"
    "ensures (forall q: ref :: {$base(q)} $sle.ref.bool(p, q) && "
    "$slt.ref.bool(q, $add.ref(p, n)) ==> $base(q) == p);\n");

  D("procedure $free(p: ref);\n"
    "modifies $Alloc, $allocatedCounter;\n"
    "requires $eq.ref.bool(p, $0.ref) || ($slt.ref.bool($0.ref, p) && "
    "$eq.ref.bool($base(p), p) && $Alloc[p]);\n"
    "ensures $ne.ref.bool(p, $0.ref) ==> !$Alloc[p];\n"
    "ensures $ne.ref.bool(p, $0.ref) ==> (forall q: ref :: {$Alloc[q]} q != p "
    "==> $Alloc[q] == old($Alloc[q]));\n"
    "ensures $ne.ref.bool(p, $0.ref) ==> $allocatedCounter == "
    "old($allocatedCounter) - 1;\n"
    "ensures $eq.ref.bool(p, $0.ref) ==> $allocatedCounter == "
    "old($allocatedCounter);\n");

#else // NO_REUSE does not reuse previously-allocated addresses
  D("var $Alloc: [ref] bool;");
  D("function $Size(ref) returns (ref);");
  D("var $CurrAddr:ref;\n");

  // LLVM does not allocated globals explicitly. Hence, we do it in our prelude
  // before the program starts using the $galloc procedure.
  D("procedure $galloc(base_addr: ref, size: ref);\n"
    "modifies $Alloc;\n"
    "ensures $Size(base_addr) == size;\n"
    "ensures (forall addr: ref :: {$base(addr)} $sle.ref.bool(base_addr, addr) "
    "&& $slt.ref.bool(addr, $add.ref(base_addr, size)) ==> $base(addr) == "
    "base_addr);\n"
    "ensures $Alloc[base_addr];\n"
    "ensures (forall q: ref :: {$Alloc[q]} q != base_addr ==> $Alloc[q] == "
    "old($Alloc[q]));\n");

  D("procedure {:inline 1} $$alloc(n: ref) returns (p: ref);\n"
    "modifies $Alloc, $CurrAddr;\n"
    "ensures $sle.ref.bool($0.ref, n);\n"
    "ensures $slt.ref.bool($0.ref, n) ==> $sge.ref.bool($sub.ref($CurrAddr, "
    "n), old($CurrAddr)) && p == old($CurrAddr);\n"
    "ensures $sgt.ref.bool($CurrAddr, $0.ref) && $slt.ref.bool($CurrAddr, "
    "$MALLOC_TOP);\n"
    "ensures $slt.ref.bool($0.ref, n) ==> $Size(p) == n;\n"
    "ensures $slt.ref.bool($0.ref, n) ==> (forall q: ref :: {$base(q)} "
    "$sle.ref.bool(p, q) && $slt.ref.bool(q, $add.ref(p, n)) ==> $base(q) == "
    "p);\n"
    "ensures $slt.ref.bool($0.ref, n) ==> $Alloc[p];\n"
    "ensures $eq.ref.bool(n, $0.ref) ==> old($CurrAddr) == $CurrAddr && p == "
    "$0.ref;\n"
    "ensures $eq.ref.bool(n, $0.ref)==> $Alloc[p] == old($Alloc)[p];\n"
    "ensures (forall q: ref :: {$Alloc[q]} q != p ==> $Alloc[q] == "
    "old($Alloc[q]));\n");

  D("procedure $free(p: ref);\n"
    "modifies $Alloc, $allocatedCounter;\n"
    "requires $eq.ref.bool(p, $0.ref) || ($slt.ref.bool($0.ref, p) && "
    "$eq.ref.bool($base(p), p) && $Alloc[p]);\n"
    "ensures $ne.ref.bool(p, $0.ref) ==> !$Alloc[p];\n"
    "ensures $ne.ref.bool(p, $0.ref) ==> (forall q: ref :: {$Alloc[q]} q != p "
    "==> $Alloc[q] == old($Alloc[q]));\n"
    "ensures $ne.ref.bool(p, $0.ref) ==> $allocatedCounter == "
    "old($allocatedCounter) - 1;\n"
    "ensures $eq.ref.bool(p, $0.ref) ==> $allocatedCounter == "
    "old($allocatedCounter);\n");
#endif

#else
  D("procedure $malloc(n: ref) returns (p: ref)\n"
    "{\n"
    "  call corral_atomic_begin();\n"
    "  call p := $$alloc(n);\n"
    "  call corral_atomic_end();\n"
    "}\n");

#if MEMORY_MODEL_NO_REUSE_IMPLS
  D("var $CurrAddr:ref;\n");

  D("procedure {:inline 1} $$alloc(n: ref) returns (p: ref)\n"
    "modifies $CurrAddr;\n"
    "{\n"
    "  assume $sge.ref.bool(n, $0.ref);\n"
    "  if ($sgt.ref.bool(n, $0.ref)) {\n"
    "    p := $CurrAddr;\n"
    "    havoc $CurrAddr;\n"
    "    assume $sge.ref.bool($sub.ref($CurrAddr, n), p);\n"
    "    assume $sgt.ref.bool($CurrAddr, $0.ref) && $slt.ref.bool($CurrAddr, "
    "$MALLOC_TOP);\n"
    "  }\n"
    "}\n");

  D("procedure $free(p: ref);\n");

#elif MEMORY_MODEL_REUSE // can reuse previously-allocated and freed addresses
  D("var $Alloc: [ref] bool;");
  D("var $Size: [ref] ref;\n");

  D("procedure {:inline 1} $$alloc(n: ref) returns (p: ref);\n"
    "modifies $Alloc, $Size;\n"
    "ensures $sle.ref.bool($0.ref, n);\n"
    "ensures $slt.ref.bool($0.ref, n) ==> $slt.ref.bool($0.ref, p) && "
    "$slt.ref.bool(p, $sub.ref($MALLOC_TOP, n));\n"
    "ensures $eq.ref.bool(n, $0.ref) ==> p == $0.ref;\n"
    "ensures !old($Alloc[p]);\n"
    "ensures (forall q: ref :: old($Alloc[q]) ==> ($slt.ref.bool($add.ref(p, "
    "n), q) || $slt.ref.bool($add.ref(q, $Size[q]), p)));\n"
    "ensures $Alloc[p];\n"
    "ensures $Size[p] == n;\n"
    "ensures (forall q: ref :: {$Size[q]} q != p ==> $Size[q] == "
    "old($Size[q]));\n"
    "ensures (forall q: ref :: {$Alloc[q]} q != p ==> $Alloc[q] == "
    "old($Alloc[q]));\n");

  D("procedure $free(p: ref);\n"
    "modifies $Alloc;\n"
    "ensures !$Alloc[p];\n"
    "ensures (forall q: ref :: {$Alloc[q]} q != p ==> $Alloc[q] == "
    "old($Alloc[q]));\n");

#else // NO_REUSE does not reuse previously-allocated addresses
  D("var $CurrAddr:ref;\n");

  D("procedure {:inline 1} $$alloc(n: ref) returns (p: ref);\n"
    "modifies $CurrAddr;\n"
    "ensures $sle.ref.bool($0.ref, n);\n"
    "ensures $slt.ref.bool($0.ref, n) ==> $sge.ref.bool($sub.ref($CurrAddr, "
    "n), old($CurrAddr)) && p == old($CurrAddr);\n"
    "ensures $sgt.ref.bool($CurrAddr, $0.ref) && $slt.ref.bool($CurrAddr, "
    "$MALLOC_TOP);\n"
    "ensures $eq.ref.bool(n, $0.ref) ==> old($CurrAddr) == $CurrAddr && p == "
    "$0.ref;\n");

  D("procedure $free(p: ref);\n");
#endif
#endif

#undef D
}

#if MEMORY_SAFETY
void __SMACK_check_memory_leak(void) {
  __SMACK_code("assert {:valid_memtrack} $allocatedCounter == 0;");
}
#endif

void __SMACK_init_func_memory_model(void) {
#if MEMORY_MODEL_NO_REUSE || MEMORY_MODEL_NO_REUSE_IMPLS
  __SMACK_code("$CurrAddr := $1024.ref;");
#endif
#if MEMORY_SAFETY
  __SMACK_code("$allocatedCounter := 0;");
#endif
}

void __VERIFIER_atomic_begin() { __SMACK_code("call corral_atomic_begin();"); }

void __VERIFIER_atomic_end() { __SMACK_code("call corral_atomic_end();"); }
