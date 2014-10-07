#! /usr/bin/env python

import subprocess
import re
import glob
import time

def red(text):
  return '\033[0;31m' + text + '\033[0m'
  
def green(text):
  return '\033[0;32m' + text + '\033[0m'
  
def expect(file):
  for line in open(file).readlines():
    match = re.search(r'@expect (.*)',line)
    if match:
      return match.group(1)
  print red("WARNING: @expect MISSING IN %s" % file),
  return ""
  
print "Running CONTRACTS regression tests..."
print

passed = failed = 0
for test in glob.glob("*.c"):

  print "{0:>20}     :".format(test),

  # invoke SMACK
  t0 = time.time()
  cmd = ['smackverify.py', test, '--verifier=boogie']
  p = subprocess.Popen(cmd, stdout=subprocess.PIPE)

  # check SMACK output
  if re.search(expect(test), p.communicate()[0]):
    print green('PASSED') + '  [%.2fs]' % round(time.time() - t0, 2)
    passed += 1
  else:
    print red('FAILED')
    failed += 1
  
print
print 'PASSED count: ', passed
print 'FAILED count: ', failed
