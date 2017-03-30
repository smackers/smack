#! /usr/bin/env python

import subprocess
import re
import time
import json

# list of regression tests with the expected outputs
#   (filename, loop unroll)
tests = [
  ('if',                1),
  ('if2',               1),
  ('if3',               1),
  ('if4',               1),
  ('switch',            1),
  ('switch2',           1),
  ('switch3',           1),
  ('switch4',           1),
  ('func',              1),
  ('func2',             1),
  ('func3',             1),
  ('libs',              1),
  ('while',             1),
  ('while2',            3),
  ('while3',            3),
  ('do',                3),
  ('for',               5),
  ('for2',              5),
  ('break',            10),
  ('continue',         10),
  ('return',            1),
]

def red(text):
  return '\033[0;31m' + text + '\033[0m'
  
def green(text):
  return '\033[0;32m' + text + '\033[0m'

def runtests():
  passed = failed = 0
  for test in tests:
    for verifier in ['boogie-inline', 'corral']:

      ansFile = open(test[0] + ".expected")
      expected = ansFile.read()
      ansFile.close()

      print "{0:>20} {1:>16}:".format(test[0], "(" + verifier + ")"),

      # invoke smack-reach
      t0 = time.time()
      p = subprocess.Popen(['smackreach.py', test[0] + '.c',
                            '--verifier=' + verifier,
                            '--unroll=' + str(test[1]), 
                            '-o', test[0] +'.bpl', '--smackd'],
                           stdout=subprocess.PIPE)
      
      smackOutput = p.communicate()[0]
      elapsed = time.time() - t0

      # check SMACK output
      if(json.loads(expected) == json.loads(smackOutput)):
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

