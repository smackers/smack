#! /usr/bin/env python

import subprocess
import re
import time

# list of regression tests with the expected outputs
tests = [
  ('cdaudio_true.i.cil',    r'Program has no bugs'),
  ('diskperf_true.i.cil',   r'Program has no bugs'),
  ('diskperf_false.i.cil',  r'This assertion can fail'),
  ('floppy2_true.i.cil',    r'Program has no bugs'),
  ('floppy_true.i.cil',     r'Program has no bugs'),
  ('floppy_false.i.cil',    r'This assertion can fail'),
  ('kbfiltr_false.i.cil',   r'This assertion can fail'),
  ('parport_true.i.cil',    r'Program has no bugs'),
  ('parport_false.i.cil',   r'This assertion can fail')
]

def red(text):
  return '\033[0;31m' + text + '\033[0m'
 
def green(text):
  return '\033[0;32m' + text + '\033[0m'

def runtests():
  passed = failed = 0
  for test in tests:

    for mem in ['no-reuse', 'no-reuse-impls', 'reuse']:

      print "{0:>25} {1:>16}:".format(test[0], "(" + mem + ")"),

      # invoke SMACK
      t0 = time.time()
      p = subprocess.Popen(['smackverify.py', test[0] + '.c', '--verifier=corral',
                            '--mem-mod=' + mem, '--unroll=2', '--clang=-w', '-o', test[0] +'.bpl'],
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

