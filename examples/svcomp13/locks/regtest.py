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
  ('test_locks_14_unsafe',  r'0 verified, 1 errors'),
  ('test_locks_15_safe',    r'1 verified, 0 errors'),
  ('test_locks_15_unsafe',  r'0 verified, 1 errors')
]

def red(text):
  return '\033[0;31m' + text + '\033[0m'
  
def green(text):
  return '\033[0;32m' + text + '\033[0m'

passed = failed = 0
for test in tests:
    
  for mem in ['flat', 'twodim']:
    
    print "{0:>20} {1:>8}:".format(test[0], "(" + mem + ")"),

    # invoke SMACK
    p = subprocess.Popen(['smack-verified.py', test[0] + '.bc', '--verifier=boogie-inline', '--mem-mod=' + mem, '-o', test[0] +'.bpl'], stdout=subprocess.PIPE)
    smackOutput = p.communicate()[0]

    # check SMACK output
    if re.search(test[1], smackOutput):
      print green('PASSED')
      passed += 1
    else:
      print red('FAILED')
      failed += 1

print '\nPASSED count: ', passed
print 'FAILED count: ', failed

