#! /usr/bin/env python

import yaml
from os import path
import subprocess
import re
import glob
import time

VERIFIERS = ['boogie', 'corral']
MEMORY_MODELS = ['no-reuse', 'no-reuse-impls', 'reuse']
TIME_LIMIT = 10

def red(text):
  return '\033[0;31m' + text + '\033[0m'
  
def green(text):
  return '\033[0;32m' + text + '\033[0m'

def check_result(expected, actual):
  if re.search(r'verified', expected):
    return re.search(r'[1-9]\d* verified, 0 errors?|no bugs', actual)
  else:
    return re.search(r'0 verified, [1-9]\d* errors?|can fail', actual)

def metadata(file):
  m = {}
  m['skip'] = False
  m['flags'] = []
  m['verifiers'] = VERIFIERS
  m['memory'] = MEMORY_MODELS

  dirs = path.dirname(file).split('/')
  i = 1
  while i <= len(dirs):
    yaml_file = path.join(*(dirs + ['config.yml']))
    if path.isfile(yaml_file):
      with open(yaml_file, "r") as f:
        data = yaml.safe_load(f)
        if 'flags' in data:
          for flag in data['flags']:
            m['flags'] += [flag]
    i += 1

  for line in open(file).readlines():
    match = re.search(r'@skip', line)
    if match:
      m['skip'] = True

    match = re.search(r'@flag (.*)',line)
    if match:
      m['flags'] += [match.group(1)]

    match = re.search(r'@expect (.*)',line)
    if match:
      m['expect'] = match.group(1)

  if not 'expect' in m:
    print red("WARNING: @expect MISSING IN %s" % file)
    m['expect'] = 'verified'

  return m
  
print "Running regression tests..."
print

passed = failed = 0
for test in glob.glob("**/*.c"):
  meta = metadata(test)

  if meta['skip']:
    continue

  print "{0:>20}".format(test)

  cmd = ['smackverify.py', test]
  cmd += ['--time-limit', str(TIME_LIMIT)]
  cmd += meta['flags']

  for memory in meta['memory']:
    cmd += ['--mem-mod=' + memory]

    for verifier in meta['verifiers']:
      cmd += ['--verifier=' + verifier]

      print "{0:>20} {1:>10}    :".format(memory, verifier),

      t0 = time.time()
      p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
      result = p.communicate()[0]
      elapsed = time.time() - t0

      if check_result(meta['expect'], result):
        print green('PASSED') + '  [%.2fs]' % round(elapsed, 2)
        passed += 1
      else:
        print red('FAILED')
        failed += 1
  
print
print 'PASSED count: ', passed
print 'FAILED count: ', failed
