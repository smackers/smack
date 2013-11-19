#! /usr/bin/env python

import subprocess
import re

# list of regression tests with the expected outputs
tests = [
  ('simple',             r'1 verified, 0 errors?'),
  ('simple_fail',        r'0 verified, 1 errors?'),
  ('simple_pre',         r'1 verified, 0 errors?'),
  ('simple_pre_fail',    r'0 verified, 1 errors?'),
  ('simple_pre1',        r'1 verified, 0 errors?'),
  ('simple_pre1_fail',   r'0 verified, 1 errors?'),
  ('simple_pre2',        r'1 verified, 0 errors?'),
  ('simple_pre2_fail',   r'0 verified, 1 errors?'),
  ('simple_pre3',        r'1 verified, 0 errors?'),
  ('simple_pre3_fail',   r'0 verified, 1 errors?'),
  ('simple_double_free', r'0 verified, 1 errors?'),
  ('pointers',           r'1 verified, 0 errors?'),
  ('pointers_fail',      r'0 verified, 1 errors?'),
  ('pointers1',          r'1 verified, 0 errors?'),
  ('pointers1_fail',     r'0 verified, 1 errors?'),
  ('pointers2',          r'1 verified, 0 errors?'),
  ('pointers2_fail',     r'0 verified, 1 errors?'),
  ('pointers3',          r'1 verified, 0 errors?'),
  ('pointers3_fail',     r'0 verified, 1 errors?'),
  ('globals',            r'1 verified, 0 errors?'),
  ('globals_fail',       r'0 verified, 1 errors?'),
  ('loop',               r'1 verified, 0 errors?'),
  ('loop_fail',          r'0 verified, 1 errors?'),
  ('loop1',              r'1 verified, 0 errors?'),
  ('loop1_fail',         r'0 verified, 1 errors?'),
  ('nondet',             r'1 verified, 0 errors?'),
  ('printfs',            r'1 verified, 0 errors?'),
  ('extern_func',        r'1 verified, 0 errors?'),
  ('return_label',       r'1 verified, 0 errors?'),
  ('struct_cast',        r'1 verified, 0 errors?'),
  ('struct_cast_fail',   r'0 verified, 1 errors?'),
  ('struct_cast1',       r'1 verified, 0 errors?'),
  ('struct_cast1_fail',  r'0 verified, 1 errors?'),
  ('nested_struct',      r'1 verified, 0 errors?'),
  ('nested_struct_fail', r'0 verified, 1 errors?'),
  ('nested_struct1',     r'1 verified, 0 errors?'),
  ('nested_struct1_fail',r'0 verified, 1 errors?'),
  ('nested_struct2',     r'1 verified, 0 errors?'),
  ('nested_struct2_fail',r'0 verified, 1 errors?'),
  ('struct_assign',      r'1 verified, 0 errors?'),
  ('struct_assign_fail', r'0 verified, 1 errors?'),
  ('func_ptr',           r'1 verified, 0 errors?'),
  ('func_ptr_fail',      r'0 verified, 1 errors?'),
  ('func_ptr1',          r'1 verified, 0 errors?'),
  ('func_ptr1_fail',     r'0 verified, 1 errors?'),
  ('array',              r'1 verified, 0 errors?'),
  ('array1',             r'1 verified, 0 errors?'),
  ('array1_fail',        r'0 verified, 1 errors?'),
  ('array2',             r'1 verified, 0 errors?'),
  ('array2_fail',        r'0 verified, 1 errors?'),
  ('array3',             r'1 verified, 0 errors?'),
  ('array3_fail',        r'0 verified, 1 errors?'),
  ('array4',             r'1 verified, 0 errors?'),
  ('array4_fail',        r'0 verified, 1 errors?'),
  ('array_free',         r'1 verified, 0 errors?'),
  ('array_free_fail',    r'0 verified, 3 errors?'),
  ('array_free1',        r'1 verified, 0 errors?'),
  ('array_free1_fail',   r'0 verified, 4 errors?'),
  ('array_free2',        r'1 verified, 0 errors?'),
  ('array_free2_fail',   r'0 verified, 5 errors?'),
  ('lock',               r'1 verified, 0 errors?'),
  ('lock_fail',          r'0 verified, 1 errors?'),
  ('ase_example',        r'1 verified, 0 errors?'),
  ('ase_example_fail',   r'0 verified, 1 errors?'),
  ('two_arrays',         r'1 verified, 0 errors?'),
  ('two_arrays1',        r'1 verified, 0 errors?'),
  ('two_arrays2',        r'1 verified, 0 errors?'),
  ('two_arrays3',        r'1 verified, 0 errors?'),
  ('two_arrays4',        r'1 verified, 0 errors?'),
  ('two_arrays5',        r'1 verified, 0 errors?'),
  ('two_arrays6',        r'1 verified, 0 errors?'),
  ('two_arrays6_fail',   r'0 verified, 1 errors?')
]

def red(text):
  return '\033[0;31m' + text + '\033[0m'
  
def green(text):
  return '\033[0;32m' + text + '\033[0m'

def runtests():
  passed = failed = 0
  for test in tests:
    
    for mem in ['flat', 'twodim']:
    
      print "{0:>20} {1:>8}:".format(test[0], "(" + mem + ")"),

      # invoke SMACK
      p = subprocess.Popen(['smack-verify.py', test[0] + '.bc', '--verifier=boogie-inline',
                            '--mem-mod=' + mem, '-o', test[0] +'.bpl'],
                            stdout=subprocess.PIPE)
      
      smackOutput = p.communicate()[0]

      # check SMACK output
      if re.search(test[1], smackOutput):
        print green('PASSED')
        passed += 1
      else:
        print red('FAILED')
        failed += 1
  
  return passed, failed

if __name__ == '__main__':

  passed, failed = runtests()
  
  print '\nPASSED count: ', passed
  print 'FAILED count: ', failed

