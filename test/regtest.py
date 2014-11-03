#! /usr/bin/env python

import subprocess
import re
import argparse
import time
from collections import namedtuple
import os.path

RegTest = namedtuple('RegTest', 'name boogie corral duality unroll')

# list of regression tests with the expected outputs
tests = [
  RegTest('hello',                 r'1 verified, 0 errors?', r'Program has no bugs', r'Program has no bugs', 2),
  RegTest('hello_fail',            r'0 verified, 1 errors?', r'This assertion can fail', r'This assertion can fail', 2),
  RegTest('simple',                r'1 verified, 0 errors?', r'Program has no bugs', r'Program has no bugs', 2),
  RegTest('simple_fail',           r'0 verified, 1 errors?', r'This assertion can fail', r'This assertion can fail', 2),
  RegTest('simple_pre',            r'1 verified, 0 errors?', r'Program has no bugs', r'Program has no bugs', 2),
  RegTest('simple_pre_fail',       r'0 verified, 1 errors?', r'This assertion can fail', r'This assertion can fail', 2),
  RegTest('simple_pre1',           r'1 verified, 0 errors?', r'Program has no bugs', r'Program has no bugs', 2),
  RegTest('simple_pre1_fail',      r'0 verified, 1 errors?', r'This assertion can fail', r'This assertion can fail', 2),
  RegTest('simple_pre2',           r'1 verified, 0 errors?', r'Program has no bugs', r'Program has no bugs', 2),
  RegTest('simple_pre2_fail',      r'0 verified, 1 errors?', r'This assertion can fail', r'This assertion can fail', 2),
  RegTest('simple_pre3',           r'1 verified, 0 errors?', r'Program has no bugs', r'Program has no bugs', 2),
  RegTest('simple_pre3_fail',      r'0 verified, 1 errors?', r'This assertion can fail', r'This assertion can fail', 2),
#  RegTest('simple_double_free',    r'0 verified, 1 errors?', r'This assertion can fail', r'This assertion can fail', 2),
  RegTest('pointers',              r'1 verified, 0 errors?', r'Program has no bugs', r'Program has no bugs', 2),
  RegTest('pointers_fail',         r'0 verified, 1 errors?', r'This assertion can fail', r'This assertion can fail', 2),
  RegTest('pointers1',             r'1 verified, 0 errors?', r'Program has no bugs', r'Program has no bugs', 2),
  RegTest('pointers1_fail',        r'0 verified, 1 errors?', r'This assertion can fail', r'This assertion can fail', 2),
  RegTest('pointers2',             r'1 verified, 0 errors?', r'Program has no bugs', r'Program has no bugs', 2),
  RegTest('pointers2_fail',        r'0 verified, 1 errors?', r'This assertion can fail', r'This assertion can fail', 2),
  RegTest('pointers3',             r'1 verified, 0 errors?', r'Program has no bugs', r'Program has no bugs', 2),
  RegTest('pointers3_fail',        r'0 verified, 1 errors?', r'This assertion can fail', r'This assertion can fail', 2),
  RegTest('globals',               r'1 verified, 0 errors?', r'Program has no bugs', r'Program has no bugs', 2),
  RegTest('globals_fail',          r'0 verified, 1 errors?', r'This assertion can fail', r'This assertion can fail', 2),
  RegTest('loop',                  r'1 verified, 0 errors?', r'Program has no bugs', r'Program has no bugs', 11),
  RegTest('loop_fail',             r'0 verified, 1 errors?', r'This assertion can fail', r'This assertion can fail', 11),
  RegTest('loop1',                 r'1 verified, 0 errors?', r'Program has no bugs', r'Program has no bugs', 11),
  RegTest('loop1_fail',            r'0 verified, 1 errors?', r'This assertion can fail', r'This assertion can fail', 11),
  RegTest('nondet',                r'1 verified, 0 errors?', r'Program has no bugs', r'Program has no bugs', 2),
  RegTest('printfs',               r'1 verified, 0 errors?', r'Program has no bugs', r'Program has no bugs', 2),
  RegTest('struct_return',         r'1 verified, 0 errors?', r'Program has no bugs', r'Program has no bugs', 2),
  RegTest('struct_init',           r'1 verified, 0 errors?', r'Program has no bugs', r'Program has no bugs', 2),
  RegTest('struct_init_fail',      r'0 verified, 1 errors?', r'This assertion can fail', r'This assertion can fail', 2),
  RegTest('extern_struct',         r'0 verified, 1 errors?', r'This assertion can fail', r'This assertion can fail', 2),
  RegTest('extern_func',           r'1 verified, 0 errors?', r'Program has no bugs', r'Program has no bugs', 2),
  RegTest('extern_mem',            r'1 verified, 0 errors?', r'Program has no bugs', r'Program has no bugs', 2),
  RegTest('extern_mem_fail',       r'0 verified, 1 errors?', r'This assertion can fail', r'This assertion can fail', 2),
  RegTest('smack_code_call',       r'1 verified, 0 errors?', r'Program has no bugs', r'Program has no bugs', 2),
  RegTest('smack_code_call_fail',  r'0 verified, 1 errors?', r'This assertion can fail', r'This assertion can fail', 2),
  RegTest('return_label',          r'1 verified, 0 errors?', r'Program has no bugs', r'Program has no bugs', 2),
  RegTest('struct_cast',           r'1 verified, 0 errors?', r'Program has no bugs', r'Program has no bugs', 2),
  RegTest('struct_cast_fail',      r'0 verified, 1 errors?', r'This assertion can fail', r'This assertion can fail', 2),
  RegTest('struct_cast1',          r'1 verified, 0 errors?', r'Program has no bugs', r'Program has no bugs', 2),
  RegTest('struct_cast1_fail',     r'0 verified, 1 errors?', r'This assertion can fail', r'This assertion can fail', 2),
  RegTest('nested_struct',         r'1 verified, 0 errors?', r'Program has no bugs', r'Program has no bugs', 2),
  RegTest('nested_struct_fail',    r'0 verified, 1 errors?', r'This assertion can fail', r'This assertion can fail', 2),
  RegTest('nested_struct1',        r'1 verified, 0 errors?', r'Program has no bugs', r'Program has no bugs', 2),
  RegTest('nested_struct1_fail',   r'0 verified, 1 errors?', r'This assertion can fail', r'This assertion can fail', 2),
  RegTest('nested_struct2',        r'1 verified, 0 errors?', r'Program has no bugs', r'Program has no bugs', 2),
  RegTest('nested_struct2_fail',   r'0 verified, 1 errors?', r'This assertion can fail', r'This assertion can fail', 2),
  RegTest('struct_assign',         r'1 verified, 0 errors?', r'Program has no bugs', r'Program has no bugs', 2),
  RegTest('struct_assign_fail',    r'0 verified, 1 errors?', r'This assertion can fail', r'This assertion can fail', 2),
  RegTest('func_ptr',              r'1 verified, 0 errors?', r'Program has no bugs', r'Program has no bugs', 2),
  RegTest('func_ptr_fail',         r'0 verified, 1 errors?', r'This assertion can fail', r'This assertion can fail', 2),
  RegTest('func_ptr1',             r'1 verified, 0 errors?', r'Program has no bugs', r'Program has no bugs', 2),
  RegTest('func_ptr1_fail',        r'0 verified, 1 errors?', r'This assertion can fail', r'This assertion can fail', 2),
  RegTest('array',                 r'1 verified, 0 errors?', r'Program has no bugs', r'Program has no bugs', 2),
  RegTest('array1',                r'1 verified, 0 errors?', r'Program has no bugs', r'Program has no bugs', 2),
  RegTest('array1_fail',           r'0 verified, 1 errors?', r'This assertion can fail', r'This assertion can fail', 2),
  RegTest('array2',                r'1 verified, 0 errors?', r'Program has no bugs', r'Program has no bugs', 11),
  RegTest('array2_fail',           r'0 verified, 1 errors?', r'This assertion can fail', r'This assertion can fail', 11),
  RegTest('array3',                r'1 verified, 0 errors?', r'Program has no bugs', r'Program has no bugs', 11),
  RegTest('array3_fail',           r'0 verified, 1 errors?', r'This assertion can fail', r'This assertion can fail', 11),
  RegTest('array4',                r'1 verified, 0 errors?', r'Program has no bugs', r'Program has no bugs', 11),
  RegTest('array4_fail',           r'0 verified, 1 errors?', r'This assertion can fail', r'This assertion can fail', 11),
#  RegTest('array_free',            r'1 verified, 0 errors?', r'Program has no bugs', r'Program has no bugs', 11),
#  RegTest('array_free_fail',       r'0 verified, 3 errors?', r'This assertion can fail', r'This assertion can fail', 11),
#  RegTest('array_free1',           r'1 verified, 0 errors?', r'Program has no bugs', r'Program has no bugs', 11),
#  RegTest('array_free1_fail',      r'0 verified, 4 errors?', r'This assertion can fail', r'This assertion can fail', 11),
#  RegTest('array_free2',           r'1 verified, 0 errors?', r'Program has no bugs', r'Program has no bugs', 11),
#  RegTest('array_free2_fail',      r'0 verified, 5 errors?', r'This assertion can fail', r'This assertion can fail', 11),
  RegTest('lock',                  r'1 verified, 0 errors?', r'Program has no bugs', r'Program has no bugs', 2),
  RegTest('lock_fail',             r'0 verified, 1 errors?', r'This assertion can fail', r'This assertion can fail', 2),
  RegTest('ase_example',           r'1 verified, 0 errors?', r'Program has no bugs', r'Program has no bugs', 11),
  RegTest('ase_example_fail',      r'0 verified, 1 errors?', r'This assertion can fail', r'This assertion can fail', 11),
  RegTest('two_arrays',            r'1 verified, 0 errors?', r'Program has no bugs', r'Program has no bugs', 2),
  RegTest('two_arrays1',           r'1 verified, 0 errors?', r'Program has no bugs', r'Program has no bugs', 2),
  RegTest('two_arrays2',           r'1 verified, 0 errors?', r'Program has no bugs', r'Program has no bugs', 2),
  RegTest('two_arrays3',           r'1 verified, 0 errors?', r'Program has no bugs', r'Program has no bugs', 2),
  RegTest('two_arrays4',           r'1 verified, 0 errors?', r'Program has no bugs', r'Program has no bugs', 2),
  RegTest('two_arrays5',           r'1 verified, 0 errors?', r'Program has no bugs', r'Program has no bugs', 2),
  RegTest('two_arrays6',           r'1 verified, 0 errors?', r'Program has no bugs', r'Program has no bugs', 2),
  RegTest('two_arrays6_fail',      r'0 verified, 1 errors?', r'This assertion can fail', r'This assertion can fail', 2),
  RegTest('floats_in_memory',      r'1 verified, 0 errors?', r'Program has no bugs', r'Program has no bugs', 2),
  RegTest('floats_in_memory_fail', r'0 verified, 1 errors?', r'This assertion can fail', r'This assertion can fail', 2)
]

def red(text):
  return '\033[0;31m' + text + '\033[0m'

def green(text):
  return '\033[0;32m' + text + '\033[0m'

def runtests(verifier):
  passed = failed = 0
  for test in tests:
    
    for mem in ['no-reuse', 'no-reuse-impls', 'reuse']:
    
      print "{0:>25} {1:>16}:".format(test.name, "(" + mem + ")"),

      if os.path.isfile(test.name + '.c'):
        sourceFile = test.name + '.c'
      elif os.path.isfile(test.name + '.cc'):
        sourceFile = test.name + '.cc'
      elif os.path.isfile(test[0] + '.cpp'):
        sourceFile = test.name + '.cpp'

      # invoke SMACK
      t0 = time.time()
      p = subprocess.Popen(['smackverify.py', sourceFile, '--verifier=' + verifier,
                            '--unroll=' + str(test.unroll), '--mem-mod=' + mem, '-o', test.name +'.bpl'],
                            stdout=subprocess.PIPE)
      
      smackOutput = p.communicate()[0]
      elapsed = time.time() - t0

      # check SMACK output
      if re.search(getattr(test, verifier), smackOutput):
        print green('PASSED') + '  [%.2fs]' % round(elapsed, 2)
        passed += 1
      else:
        print red('FAILED')
        failed += 1
  
  return passed, failed

if __name__ == '__main__':

  # parse command line arguments
  parser = argparse.ArgumentParser(description='Runs regressions in this folder.')
  parser.add_argument('--verifier', dest='verifier', choices=['boogie', 'corral', 'duality'], default=['corral'], nargs='*',
                      help='choose verifiers to be used')
  args = parser.parse_args()

  for verifier in args.verifier:
    print '\nRunning regressions using', verifier
    passed, failed = runtests(verifier)
  
    print '\nPASSED count: ', passed
    print 'FAILED count: ', failed

