#! /usr/bin/env python

import subprocess
import re

# list of regression tests with the expected outputs
tests = [
  ('test_locks_5_safe',     r'1 verified, 0 errors'),
  ('test_locks_6_safe',     r'1 verified, 0 errors'),
  ('test_locks_7_safe',     r'1 verified, 0 errors'),
  ('test_locks_8_safe',     r'1 verified, 0 errors'),
  ('test_locks_9_safe',     r'1 verified, 0 errors'),
  ('test_locks_10_safe',    r'1 verified, 0 errors'),
  ('test_locks_11_safe',    r'1 verified, 0 errors'),
  ('test_locks_12_safe',    r'1 verified, 0 errors'),
  ('test_locks_13_safe',    r'1 verified, 0 errors'),
  ('test_locks_14_safe',    r'1 verified, 0 errors'),
  ('test_locks_14_unsafe',  r'0 verified, 1 error' ),
  ('test_locks_15_safe',    r'1 verified, 0 errors'),
  ('test_locks_15_unsafe',  r'0 verified, 1 error' )
]


for test in tests:

  # invoke SMACK
  p = subprocess.Popen(['smack-check.py', test[0] + '.o', '-o', test[0] +'.bpl'], stdout=subprocess.PIPE)
  smackOutput = p.communicate()[0]

  # check SMACK output
  if re.search(test[1], smackOutput):
    print 'PASSED: ', test[0]
  else:
    print 'FAILED: ', test[0]

