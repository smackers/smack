#! /usr/bin/env python

import subprocess
import re

# list of regression tests with the expected outputs
tests = [
  ('simple.ll',             r'1 verified, 0 errors'),
  ('simple_fail.ll',        r'0 verified, 1 error' ),
  ('simple_pre.ll',         r'1 verified, 0 errors'),
  ('simple_pre_fail.ll',    r'0 verified, 1 error' ),
  ('simple_pre1.ll',        r'1 verified, 0 errors'),
  ('simple_pre1_fail.ll',   r'0 verified, 1 error' ),
  ('simple_pre2.ll',        r'1 verified, 0 errors'),
  ('simple_pre2_fail.ll',   r'0 verified, 1 error' ),
  ('simple_pre3.ll',        r'1 verified, 0 errors'),
  ('simple_pre3_fail.ll',   r'0 verified, 1 error' ),
  ('simple_double_free.ll', r'0 verified, 1 error' ),
  ('pointers.ll',           r'1 verified, 0 errors'),
  ('pointers_fail.ll',      r'0 verified, 1 error' ),
  ('pointers1.ll',          r'1 verified, 0 errors'),
  ('pointers1_fail.ll',     r'0 verified, 1 error' ),
  ('pointers2.ll',          r'1 verified, 0 errors'),
  ('pointers2_fail.ll',     r'0 verified, 1 error' ),
  ('pointers3.ll',          r'1 verified, 0 errors'),
  ('pointers3_fail.ll',     r'0 verified, 1 error' ),
  ('loop.ll',               r'1 verified, 0 errors'),
  ('loop_fail.ll',          r'0 verified, 1 error' ),
  ('loop1.ll',              r'1 verified, 0 errors'),
  ('loop1_fail.ll',         r'0 verified, 1 error' ),
  ('nondet.ll',             r'1 verified, 0 errors'),
  ('printfs.ll',            r'1 verified, 0 errors'),
  ('return_label.ll',       r'1 verified, 0 errors'),
  ('func_ptr.ll',           r'1 verified, 0 errors'),
  ('func_ptr_fail.ll',      r'0 verified, 1 error' ),
  ('func_ptr1.ll',          r'1 verified, 0 errors'),
  ('func_ptr1_fail.ll',     r'0 verified, 1 error' ),
  ('array.ll',              r'1 verified, 0 errors'),
  ('array1.ll',             r'1 verified, 0 errors'),
  ('array1_fail.ll',        r'0 verified, 1 error' ),
  ('array2.ll',             r'1 verified, 0 errors'),
  ('array2_fail.ll',        r'0 verified, 1 error' ),
  ('array3.ll',             r'1 verified, 0 errors'),
  ('array3_fail.ll',        r'0 verified, 1 error' ),
  ('array4.ll',             r'1 verified, 0 errors'),
  ('array4_fail.ll',        r'0 verified, 1 error' ),
  ('array_free.ll',         r'1 verified, 0 errors'),
  ('array_free_fail.ll',    r'0 verified, 3 errors'),
  ('array_free1.ll',        r'1 verified, 0 errors'),
  ('array_free1_fail.ll',   r'0 verified, 4 errors'),
  ('array_free2.ll',        r'1 verified, 0 errors'),
  ('array_free2_fail.ll',   r'0 verified, 5 errors'),
  ('two_arrays.ll',         r'1 verified, 0 errors'),
  ('two_arrays1.ll',        r'1 verified, 0 errors'),
  ('two_arrays2.ll',        r'1 verified, 0 errors'),
  ('two_arrays3.ll',        r'1 verified, 0 errors'),
  ('two_arrays4.ll',        r'1 verified, 0 errors'),
  ('two_arrays5.ll',        r'1 verified, 0 errors'),
  ('two_arrays6.ll',        r'1 verified, 0 errors'),
  ('two_arrays6_fail.ll',   r'0 verified, 1 error' )
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

