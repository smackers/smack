#! /usr/bin/env python

import subprocess
import re
import time

# list of regression tests with the expected outputs
#  [(filename, outputFilter, unroll, context-switches), (...)]
tests = [
  ('no_lock',               r'This assertion can fail', 1, 2),
  ('no_lock2',              r'This assertion can fail', 1, 2),
  ('lock',                  r'Program has no bugs', 1, 2),
  ('lock2',                 r'Program has no bugs', 1, 5),
  ('lock3',                 r'Program has no bugs', 1, 2),
  ('no_join',               r'This assertion can fail', 1, 2),
  ('join',                  r'Program has no bugs', 1, 2),
  ('fib3_false',            r'Program has no bugs', 1, 2),
  ('fib3_false',            r'This assertion can fail', 1, 3),
  ('fib3_true',             r'Program has no bugs', 1, 3),
  ('fib4_false',            r'Program has no bugs', 1, 3),
  ('fib4_false',            r'This assertion can fail', 1, 4),
  ('fib4_true',             r'Program has no bugs', 1, 4),

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

