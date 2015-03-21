#! /usr/bin/env python

import subprocess
import re
import argparse
import time
from collections import namedtuple

RegTest = namedtuple('RegTest', 'name boogie corral duality unroll')

# list of regression tests with the expected outputs
tests = [
  RegTest('test_locks_5_true',     r'1 verified, 0 errors?', r'Program has no bugs', r'Program has no bugs', 2),
  RegTest('test_locks_6_true',     r'1 verified, 0 errors?', r'Program has no bugs', r'Program has no bugs', 2),
  RegTest('test_locks_7_true',     r'1 verified, 0 errors?', r'Program has no bugs', r'Program has no bugs', 2),
  RegTest('test_locks_8_true',     r'1 verified, 0 errors?', r'Program has no bugs', r'Program has no bugs', 2),
  RegTest('test_locks_9_true',     r'1 verified, 0 errors?', r'Program has no bugs', r'Program has no bugs', 2),
  RegTest('test_locks_10_true',    r'1 verified, 0 errors?', r'Program has no bugs', r'Program has no bugs', 2),
  RegTest('test_locks_11_true',    r'1 verified, 0 errors?', r'Program has no bugs', r'Program has no bugs', 2),
  RegTest('test_locks_12_true',    r'1 verified, 0 errors?', r'Program has no bugs', r'Program has no bugs', 2),
  RegTest('test_locks_13_true',    r'1 verified, 0 errors?', r'Program has no bugs', r'Program has no bugs', 2),
  RegTest('test_locks_14_true',    r'1 verified, 0 errors?', r'Program has no bugs', r'Program has no bugs', 2),
  RegTest('test_locks_14_false',   r'0 verified, 1 errors?', r'This assertion can fail', r'This assertion can fail', 2),
  RegTest('test_locks_15_true',    r'1 verified, 0 errors?', r'Program has no bugs', r'Program has no bugs', 2),
  RegTest('test_locks_15_false',   r'0 verified, 1 errors?', r'This assertion can fail', r'This assertion can fail', 2)
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

      # invoke SMACK
      t0 = time.time()
      p = subprocess.Popen(['smackverify.py', test.name + '.c', '--verifier=' + verifier,
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

