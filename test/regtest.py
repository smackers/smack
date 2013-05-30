#! /usr/bin/env python

import subprocess
import re

# list of regression tests with the expected outputs
tests = [
  ('simple.bc',             r'1 verified, 0 errors'),
  ('simple_fail.bc',        r'0 verified, 1 error' ),
  ('simple_pre.bc',         r'1 verified, 0 errors'),
  ('simple_pre_fail.bc',    r'0 verified, 1 error' ),
  ('simple_pre1.bc',        r'1 verified, 0 errors'),
  ('simple_pre1_fail.bc',   r'0 verified, 1 error' ),
  ('simple_pre2.bc',        r'1 verified, 0 errors'),
  ('simple_pre2_fail.bc',   r'0 verified, 1 error' ),
  ('simple_pre3.bc',        r'1 verified, 0 errors'),
  ('simple_pre3_fail.bc',   r'0 verified, 1 error' ),
  ('simple_double_free.bc', r'0 verified, 1 error' ),
  ('pointers.bc',           r'1 verified, 0 errors'),
  ('pointers_fail.bc',      r'0 verified, 1 error' ),
  ('pointers1.bc',          r'1 verified, 0 errors'),
  ('pointers1_fail.bc',     r'0 verified, 1 error' ),
  ('pointers2.bc',          r'1 verified, 0 errors'),
  ('pointers2_fail.bc',     r'0 verified, 1 error' ),
  ('pointers3.bc',          r'1 verified, 0 errors'),
  ('pointers3_fail.bc',     r'0 verified, 1 error' ),
  ('loop.bc',               r'1 verified, 0 errors'),
  ('loop_fail.bc',          r'0 verified, 1 error' ),
  ('loop1.bc',              r'1 verified, 0 errors'),
  ('loop1_fail.bc',         r'0 verified, 1 error' ),
  ('nondet.bc',             r'1 verified, 0 errors'),
  ('printfs.bc',            r'1 verified, 0 errors'),
  ('return_label.bc',       r'1 verified, 0 errors'),
  ('func_ptr.bc',           r'1 verified, 0 errors'),
  ('func_ptr_fail.bc',      r'0 verified, 1 error' ),
  ('func_ptr1.bc',          r'1 verified, 0 errors'),
  ('func_ptr1_fail.bc',     r'0 verified, 1 error' ),
  ('array.bc',              r'1 verified, 0 errors'),
  ('array1.bc',             r'1 verified, 0 errors'),
  ('array1_fail.bc',        r'0 verified, 1 error' ),
  ('array2.bc',             r'1 verified, 0 errors'),
  ('array2_fail.bc',        r'0 verified, 1 error' ),
  ('array3.bc',             r'1 verified, 0 errors'),
  ('array3_fail.bc',        r'0 verified, 1 error' ),
  ('array4.bc',             r'1 verified, 0 errors'),
  ('array4_fail.bc',        r'0 verified, 1 error' ),
  ('array_free.bc',         r'1 verified, 0 errors'),
  ('array_free_fail.bc',    r'0 verified, 3 errors'),
  ('array_free1.bc',        r'1 verified, 0 errors'),
  ('array_free1_fail.bc',   r'0 verified, 4 errors'),
  ('array_free2.bc',        r'1 verified, 0 errors'),
  ('array_free2_fail.bc',   r'0 verified, 5 errors'),
  ('two_arrays.bc',         r'1 verified, 0 errors'),
  ('two_arrays1.bc',        r'1 verified, 0 errors'),
  ('two_arrays2.bc',        r'1 verified, 0 errors'),
  ('two_arrays3.bc',        r'1 verified, 0 errors'),
  ('two_arrays4.bc',        r'1 verified, 0 errors'),
  ('two_arrays5.bc',        r'1 verified, 0 errors'),
  ('two_arrays6.bc',        r'1 verified, 0 errors'),
  ('two_arrays6_fail.bc',   r'0 verified, 1 error' )
]


for test in tests:

  # invoke SMACK
  p = subprocess.Popen(['smack-check.py', test[0], '-o', test[0] + '.bpl'], stdout=subprocess.PIPE)
  smackOutput = p.communicate()[0]

  # check SMACK output
  if re.search(test[1], smackOutput):
    print 'PASSED: ', test[0]
  else:
    print 'FAILED: ', test[0]

