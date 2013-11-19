#! /usr/bin/env python

import subprocess
import re

# list of regression tests with the expected outputs
tests = [
  ('simple',             r'Program has no bugs'),
  ('simple_fail',        r'This assertion can fail'),
  ('simple_pre',         r'Program has no bugs'),
  ('simple_pre_fail',    r'This assertion can fail'),
  ('simple_pre1',        r'Program has no bugs'),
  ('simple_pre1_fail',   r'This assertion can fail'),
  ('simple_pre2',        r'Program has no bugs'),
  ('simple_pre2_fail',   r'This assertion can fail'),
  ('simple_pre3',        r'Program has no bugs'),
  ('simple_pre3_fail',   r'This assertion can fail'),
  ('simple_double_free', r'This assertion can fail'),
  ('pointers',           r'Program has no bugs'),
  ('pointers_fail',      r'This assertion can fail'),
  ('pointers1',          r'Program has no bugs'),
  ('pointers1_fail',     r'This assertion can fail'),
  ('pointers2',          r'Program has no bugs'),
  ('pointers2_fail',     r'This assertion can fail'),
  ('pointers3',          r'Program has no bugs'),
  ('pointers3_fail',     r'This assertion can fail'),
  ('globals',            r'Program has no bugs'),
  ('globals_fail',       r'This assertion can fail'),
  ('loop',               r'Program has no bugs'),
  ('loop_fail',          r'This assertion can fail'),
  ('loop1',              r'Program has no bugs'),
  ('loop1_fail',         r'This assertion can fail'),
  ('nondet',             r'Program has no bugs'),
  ('printfs',            r'Program has no bugs'),
  ('extern_func',        r'Program has no bugs'),
  ('return_label',       r'Program has no bugs'),
  ('struct_cast',        r'Program has no bugs'),
  ('struct_cast_fail',   r'This assertion can fail'),
  ('struct_cast1',       r'Program has no bugs'),
  ('struct_cast1_fail',  r'This assertion can fail'),
  ('nested_struct',      r'Program has no bugs'),
  ('nested_struct_fail', r'This assertion can fail'),
  ('nested_struct1',     r'Program has no bugs'),
  ('nested_struct1_fail',r'This assertion can fail'),
  ('nested_struct2',     r'Program has no bugs'),
  ('nested_struct2_fail',r'This assertion can fail'),
  ('struct_assign',      r'Program has no bugs'),
  ('struct_assign_fail', r'This assertion can fail'),
  ('func_ptr',           r'Program has no bugs'),
  ('func_ptr_fail',      r'This assertion can fail'),
  ('func_ptr1',          r'Program has no bugs'),
  ('func_ptr1_fail',     r'This assertion can fail'),
  ('array',              r'Program has no bugs'),
  ('array1',             r'Program has no bugs'),
  ('array1_fail',        r'This assertion can fail'),
  ('array2',             r'Program has no bugs'),
  ('array2_fail',        r'This assertion can fail'),
  ('array3',             r'Program has no bugs'),
  ('array3_fail',        r'This assertion can fail'),
  ('array4',             r'Program has no bugs'),
  ('array4_fail',        r'This assertion can fail'),
  ('array_free',         r'Program has no bugs'),
  ('array_free_fail',    r'This assertion can fail'),
  ('array_free1',        r'Program has no bugs'),
  ('array_free1_fail',   r'This assertion can fail'),
  ('array_free2',        r'Program has no bugs'),
  ('array_free2_fail',   r'This assertion can fail'),
  ('lock',               r'Program has no bugs'),
  ('lock_fail',          r'This assertion can fail'),
  ('ase_example',        r'Program has no bugs'),
  ('ase_example_fail',   r'This assertion can fail'),
  ('two_arrays',         r'Program has no bugs'),
  ('two_arrays1',        r'Program has no bugs'),
  ('two_arrays2',        r'Program has no bugs'),
  ('two_arrays3',        r'Program has no bugs'),
  ('two_arrays4',        r'Program has no bugs'),
  ('two_arrays5',        r'Program has no bugs'),
  ('two_arrays6',        r'Program has no bugs'),
  ('two_arrays6_fail',   r'This assertion can fail')
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
      p = subprocess.Popen(['smack-verify.py', test[0] + '.bc', '--verifier=corral',
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

