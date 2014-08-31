#! /usr/bin/env python

import subprocess
import re
import time

# 'pass' is a python keyword, so using good
good = r'Program has no bugs'
fail = r'This assertion can fail'

# list of regression tests with the expected outputs
#  [(filename, outputFilter, unroll, context-switches), (...)]
tests = [
  ('no_lock',               fail, 1, 2),
  ('no_lock2',              fail, 1, 2),
  ('lock',                  good, 1, 2),
  ('lock2',                 good, 1, 2),
  #('lock3',                 good, 1, 2),
  ('no_join',               fail, 1, 2),
  ('join',                  good, 1, 2),
  ('join_return_fail',      fail, 1, 2),
  ('join_return_pass',      good, 1, 2),
  ('join_return2',          good, 1, 2),
  #('fib3_false',            good, 1, 2),
  #('fib3_false',            fail, 1, 3),
  #('fib3_true',             good, 1, 3),
  #('fib4_false',            good, 1, 3),
  #('fib4_false',            fail, 1, 4),
  #('fib4_true',             good, 1, 4),

]

def red(text):
  return '\033[0;31m' + text + '\033[0m'
  
def green(text):
  return '\033[0;32m' + text + '\033[0m'

def runtests():
  passed = failed = 0
  for test in tests:
    
    print "{0:>20} {1:>20}:".format(test[0], "(ContextSwitches: " + str(test[3]) + ")"),

    # invoke SMACK
    t0 = time.time()
    p = subprocess.Popen(['smackverify.py', test[0] + '.c', '--verifier=corral',
                          '--unroll=' + str(test[2]), '--mem-mod=no-reuse-impls',
                          '--context-switches', str(test[3]),
                          '-o', test[0] +'.bpl'],
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

