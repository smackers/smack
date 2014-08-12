#! /usr/bin/env python

import subprocess
import re
import time

# list of regression tests with the expected outputs
tests = [
  ('simple',                r'1 verified, 0 errors?', 2),
  ('simple_fail',           r'0 verified, 1 errors?', 2),
  ('simple_pre',            r'1 verified, 0 errors?', 2),
  ('simple_pre_fail',       r'0 verified, 1 errors?', 2),
  ('simple_pre1',           r'1 verified, 0 errors?', 2),
  ('simple_pre1_fail',      r'0 verified, 1 errors?', 2),
  ('simple_pre2',           r'1 verified, 0 errors?', 2),
  ('simple_pre2_fail',      r'0 verified, 1 errors?', 2),
  ('simple_pre3',           r'1 verified, 0 errors?', 2),
  ('simple_pre3_fail',      r'0 verified, 1 errors?', 2),
#  ('simple_double_free',    r'0 verified, 1 errors?', 2),
  ('pointers',              r'1 verified, 0 errors?', 2),
  ('pointers_fail',         r'0 verified, 1 errors?', 2),
  ('pointers1',             r'1 verified, 0 errors?', 2),
  ('pointers1_fail',        r'0 verified, 1 errors?', 2),
  ('pointers2',             r'1 verified, 0 errors?', 2),
  ('pointers2_fail',        r'0 verified, 1 errors?', 2),
  ('pointers3',             r'1 verified, 0 errors?', 2),
  ('pointers3_fail',        r'0 verified, 1 errors?', 2),
  ('globals',               r'1 verified, 0 errors?', 2),
  ('globals_fail',          r'0 verified, 1 errors?', 2),
  ('loop',                  r'1 verified, 0 errors?', 11),
  ('loop_fail',             r'0 verified, 1 errors?', 11),
  ('loop1',                 r'1 verified, 0 errors?', 11),
  ('loop1_fail',            r'0 verified, 1 errors?', 11),
  ('nondet',                r'1 verified, 0 errors?', 2),
  ('printfs',               r'1 verified, 0 errors?', 2),
  ('struct_return',         r'1 verified, 0 errors?', 2),
  ('struct_init',           r'1 verified, 0 errors?', 2),
  ('struct_init_fail',      r'0 verified, 1 errors?', 2),
  ('extern_struct',         r'0 verified, 1 errors?', 2),
  ('extern_func',           r'1 verified, 0 errors?', 2),
  ('extern_mem',            r'1 verified, 0 errors?', 2),
  ('extern_mem_fail',       r'0 verified, 1 errors?', 2),
  ('smack_code_call',       r'1 verified, 0 errors?', 2),
  ('smack_code_call_fail',  r'0 verified, 1 errors?', 2),
  ('return_label',          r'1 verified, 0 errors?', 2),
  ('struct_cast',           r'1 verified, 0 errors?', 2),
  ('struct_cast_fail',      r'0 verified, 1 errors?', 2),
  ('struct_cast1',          r'1 verified, 0 errors?', 2),
  ('struct_cast1_fail',     r'0 verified, 1 errors?', 2),
  ('nested_struct',         r'1 verified, 0 errors?', 2),
  ('nested_struct_fail',    r'0 verified, 1 errors?', 2),
  ('nested_struct1',        r'1 verified, 0 errors?', 2),
  ('nested_struct1_fail',   r'0 verified, 1 errors?', 2),
  ('nested_struct2',        r'1 verified, 0 errors?', 2),
  ('nested_struct2_fail',   r'0 verified, 1 errors?', 2),
  ('struct_assign',         r'1 verified, 0 errors?', 2),
  ('struct_assign_fail',    r'0 verified, 1 errors?', 2),
  ('func_ptr',              r'1 verified, 0 errors?', 2),
  ('func_ptr_fail',         r'0 verified, 1 errors?', 2),
  ('func_ptr1',             r'1 verified, 0 errors?', 2),
  ('func_ptr1_fail',        r'0 verified, 1 errors?', 2),
  ('array',                 r'1 verified, 0 errors?', 2),
  ('array1',                r'1 verified, 0 errors?', 2),
  ('array1_fail',           r'0 verified, 1 errors?', 2),
  ('array2',                r'1 verified, 0 errors?', 11),
  ('array2_fail',           r'0 verified, 1 errors?', 11),
  ('array3',                r'1 verified, 0 errors?', 11),
  ('array3_fail',           r'0 verified, 1 errors?', 11),
  ('array4',                r'1 verified, 0 errors?', 11),
  ('array4_fail',           r'0 verified, 1 errors?', 11),
#  ('array_free',            r'1 verified, 0 errors?', 11),
#  ('array_free_fail',       r'0 verified, 3 errors?', 11),
#  ('array_free1',           r'1 verified, 0 errors?', 11),
#  ('array_free1_fail',      r'0 verified, 4 errors?', 11),
#  ('array_free2',           r'1 verified, 0 errors?', 11),
#  ('array_free2_fail',      r'0 verified, 5 errors?', 11),
  ('lock',                  r'1 verified, 0 errors?', 2),
  ('lock_fail',             r'0 verified, 1 errors?', 2),
  ('ase_example',           r'1 verified, 0 errors?', 11),
  ('ase_example_fail',      r'0 verified, 1 errors?', 11),
  ('two_arrays',            r'1 verified, 0 errors?', 2),
  ('two_arrays1',           r'1 verified, 0 errors?', 2),
  ('two_arrays2',           r'1 verified, 0 errors?', 2),
  ('two_arrays3',           r'1 verified, 0 errors?', 2),
  ('two_arrays4',           r'1 verified, 0 errors?', 2),
  ('two_arrays5',           r'1 verified, 0 errors?', 2),
  ('two_arrays6',           r'1 verified, 0 errors?', 2),
  ('two_arrays6_fail',      r'0 verified, 1 errors?', 2)
]

def red(text):
  return '\033[0;31m' + text + '\033[0m'
  
def green(text):
  return '\033[0;32m' + text + '\033[0m'

def runtests():
  passed = failed = 0
  for test in tests:
    
    for mem in ['no-reuse', 'no-reuse-impls', 'reuse']:
    
      print "{0:>20} {1:>16}:".format(test[0], "(" + mem + ")"),

      # invoke SMACK
      t0 = time.time()
      p = subprocess.Popen(['smackverify.py', test[0] + '.c', '--verifier=boogie',
                            '--unroll=' + str(test[2]), '--mem-mod=' + mem, '-o', test[0] +'.bpl'],
                            stdout=subprocess.PIPE)
      
      smackOutput = p.communicate()[0]
      elapsed = time.time() - t0

      # check SMACK output
      if re.search(test[1], smackOutput):
        print green('PASSED') + '  [%.2fs]' % round(elapsed, 2)
        passed += 1
      else:
        print red('FAILED')
        failed += 1
  
  return passed, failed

if __name__ == '__main__':

  passed, failed = runtests()
  
  print '\nPASSED count: ', passed
  print 'FAILED count: ', failed

