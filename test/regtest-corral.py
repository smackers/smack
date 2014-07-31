#! /usr/bin/env python

import subprocess
import re
import time

# list of regression tests with the expected outputs
tests = [
  ('simple',                r'Program has no bugs', 2),
  ('simple_fail',           r'This assertion can fail', 2),
  ('simple_pre',            r'Program has no bugs', 2),
  ('simple_pre_fail',       r'This assertion can fail', 2),
  ('simple_pre1',           r'Program has no bugs', 2),
  ('simple_pre1_fail',      r'This assertion can fail', 2),
  ('simple_pre2',           r'Program has no bugs', 2),
  ('simple_pre2_fail',      r'This assertion can fail', 2),
  ('simple_pre3',           r'Program has no bugs', 2),
  ('simple_pre3_fail',      r'This assertion can fail', 2),
#  ('simple_double_free',    r'This assertion can fail', 2),
  ('pointers',              r'Program has no bugs', 2),
  ('pointers_fail',         r'This assertion can fail', 2),
  ('pointers1',             r'Program has no bugs', 2),
  ('pointers1_fail',        r'This assertion can fail', 2),
  ('pointers2',             r'Program has no bugs', 2),
  ('pointers2_fail',        r'This assertion can fail', 2),
  ('pointers3',             r'Program has no bugs', 2),
  ('pointers3_fail',        r'This assertion can fail', 2),
  ('globals',               r'Program has no bugs', 2),
  ('globals_fail',          r'This assertion can fail', 2),
  ('loop',                  r'Program has no bugs', 11),
  ('loop_fail',             r'This assertion can fail', 11),
  ('loop1',                 r'Program has no bugs', 11),
  ('loop1_fail',            r'This assertion can fail', 11),
  ('nondet',                r'Program has no bugs', 2),
  ('printfs',               r'Program has no bugs', 2),
  ('struct_return',         r'Program has no bugs', 2),
  ('struct_init',           r'Program has no bugs', 2),
  ('struct_init_fail',      r'This assertion can fail', 2),
  ('extern_struct',         r'This assertion can fail', 2),
  ('extern_func',           r'Program has no bugs', 2),
  ('extern_mem',            r'Program has no bugs', 2),
  ('extern_mem_fail',       r'This assertion can fail', 2),
  ('smack_code_call',       r'Program has no bugs', 2),
  ('smack_code_call_fail',  r'This assertion can fail', 2),
  ('return_label',          r'Program has no bugs', 2),
  ('struct_cast',           r'Program has no bugs', 2),
  ('struct_cast_fail',      r'This assertion can fail', 2),
  ('struct_cast1',          r'Program has no bugs', 2),
  ('struct_cast1_fail',     r'This assertion can fail', 2),
  ('nested_struct',         r'Program has no bugs', 2),
  ('nested_struct_fail',    r'This assertion can fail', 2),
  ('nested_struct1',        r'Program has no bugs', 2),
  ('nested_struct1_fail',   r'This assertion can fail', 2),
  ('nested_struct2',        r'Program has no bugs', 2),
  ('nested_struct2_fail',   r'This assertion can fail', 2),
  ('struct_assign',         r'Program has no bugs', 2),
  ('struct_assign_fail',    r'This assertion can fail', 2),
  ('func_ptr',              r'Program has no bugs', 2),
  ('func_ptr_fail',         r'This assertion can fail', 2),
  ('func_ptr1',             r'Program has no bugs', 2),
  ('func_ptr1_fail',        r'This assertion can fail', 2),
  ('array',                 r'Program has no bugs', 2),
  ('array1',                r'Program has no bugs', 2),
  ('array1_fail',           r'This assertion can fail', 2),
  ('array2',                r'Program has no bugs', 11),
  ('array2_fail',           r'This assertion can fail', 11),
  ('array3',                r'Program has no bugs', 11),
  ('array3_fail',           r'This assertion can fail', 11),
  ('array4',                r'Program has no bugs', 11),
  ('array4_fail',           r'This assertion can fail', 11),
#  ('array_free',            r'Program has no bugs', 11),
#  ('array_free_fail',       r'This assertion can fail', 11),
#  ('array_free1',           r'Program has no bugs', 11),
#  ('array_free1_fail',      r'This assertion can fail', 11),
#  ('array_free2',           r'Program has no bugs', 11),
#  ('array_free2_fail',      r'This assertion can fail', 11),
  ('lock',                  r'Program has no bugs', 2),
  ('lock_fail',             r'This assertion can fail', 2),
  ('ase_example',           r'Program has no bugs', 11),
  ('ase_example_fail',      r'This assertion can fail', 11),
  ('two_arrays',            r'Program has no bugs', 2),
  ('two_arrays1',           r'Program has no bugs', 2),
  ('two_arrays2',           r'Program has no bugs', 2),
  ('two_arrays3',           r'Program has no bugs', 2),
  ('two_arrays4',           r'Program has no bugs', 2),
  ('two_arrays5',           r'Program has no bugs', 2),
  ('two_arrays6',           r'Program has no bugs', 2),
  ('two_arrays6_fail',      r'This assertion can fail', 2)
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
      p = subprocess.Popen(['smackverify.py', test[0] + '.c', '--verifier=corral',
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

