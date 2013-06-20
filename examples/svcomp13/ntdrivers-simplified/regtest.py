#! /usr/bin/env python

import subprocess
import re

# list of regression tests with the expected outputs
tests = [
  ('cdaudio_simpl1_safe.cil',    r'1 verified, 0 errors'),
  ('cdaudio_simpl1_unsafe.cil',  r'0 verified, 1 error' ),
  ('diskperf_simpl1_safe.cil',   r'1 verified, 0 errors'),
  ('floppy_simpl3_safe.cil',     r'1 verified, 0 errors'),
  ('floppy_simpl3_unsafe.cil',   r'0 verified, 1 error' ),
  ('floppy_simpl4_safe.cil',     r'1 verified, 0 errors'),
  ('floppy_simpl4_unsafe.cil',   r'0 verified, 1 error' ),
  ('kbfiltr_simpl1_safe.cil',    r'1 verified, 0 errors'),
  ('kbfiltr_simpl2_safe.cil',    r'1 verified, 0 errors'),
  ('kbfiltr_simpl2_unsafe.cil',  r'0 verified, 1 error' )
]


passed = failed = 0
for test in tests:

  # invoke SMACK
  p = subprocess.Popen(['smack-check.py', test[0] + '.o', '-o', test[0] +'.bpl'], stdout=subprocess.PIPE)
  smackOutput = p.communicate()[0]

  # check SMACK output
  if re.search(test[1], smackOutput):
    print 'PASSED: ', test[0]
    passed += 1
  else:
    print 'FAILED: ', test[0]
    failed += 1

print '\nPASSED count: ', passed
print 'FAILED count: ', failed

