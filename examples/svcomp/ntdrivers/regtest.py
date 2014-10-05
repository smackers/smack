#! /usr/bin/env python

import subprocess
import re
import argparse
import time
from collections import namedtuple

RegTest = namedtuple('RegTest', 'name boogie corral duality unroll')

# list of regression tests with the expected outputs
tests = [
  RegTest('cdaudio_true.i.cil',    r'1 verified, 0 errors?', r'Program has no bugs', r'Program has no bugs', 2),
  RegTest('diskperf_true.i.cil',   r'1 verified, 0 errors?', r'Program has no bugs', r'Program has no bugs', 2),
  RegTest('diskperf_false.i.cil',  r'0 verified, 1 errors?', r'This assertion can fail', r'This assertion can fail', 2),
  RegTest('floppy2_true.i.cil',    r'1 verified, 0 errors?', r'Program has no bugs', r'Program has no bugs', 2),
  RegTest('floppy_true.i.cil',     r'1 verified, 0 errors?', r'Program has no bugs', r'Program has no bugs', 2),
  RegTest('floppy_false.i.cil',    r'0 verified, 5 errors?', r'This assertion can fail', r'This assertion can fail', 2),
  RegTest('kbfiltr_false.i.cil',   r'0 verified, 1 errors?', r'This assertion can fail', r'This assertion can fail', 2),
  RegTest('parport_true.i.cil',    r'1 verified, 0 errors?', r'Program has no bugs', r'Program has no bugs', 2),
  RegTest('parport_false.i.cil',   r'0 verified, 1 errors?', r'This assertion can fail', r'This assertion can fail', 2)
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
  parser.add_argument('--verifier', dest='verifier', choices=['boogie', 'corral', 'duality'], default=['boogie'], nargs='*',
                      help='choose verifiers to be used')
  args = parser.parse_args()

  for verifier in args.verifier:
    print '\nRunning regressions using', verifier
    passed, failed = runtests(verifier)
  
    print '\nPASSED count: ', passed
    print 'FAILED count: ', failed

