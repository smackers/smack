#! /usr/bin/env python

import yaml
from os import path
import subprocess
import re
import glob
import time

OVERRIDE_FIELDS = ['verifiers', 'memory', 'time-limit', 'skip']
APPEND_FIELDS = ['flags']

def red(text):
  return '\033[0;31m' + text + '\033[0m'
  
def green(text):
  return '\033[0;32m' + text + '\033[0m'

def check_result(expected, actual):
  if re.search(r'verified', expected):
    return re.search(r'[1-9]\d* verified, 0 errors?|no bugs', actual)
  else:
    return re.search(r'0 verified, [1-9]\d* errors?|can fail', actual)

def merge(metadata, yamldata):

  for key in OVERRIDE_FIELDS:
    if key in yamldata:
      metadata[key] = yamldata[key]

  for key in APPEND_FIELDS:
    if key in yamldata:
      if key in metadata:
        metadata[key] += yamldata[key]
      else:
        metadata[key] = yamldata[key]

def metadata(file):
  m = {}
  prefix = []

  for d in path.dirname(file).split('/'):
    prefix += [d]
    yaml_file = path.join(*(prefix + ['config.yml']))
    if path.isfile(yaml_file):
      with open(yaml_file, "r") as f:
        data = yaml.safe_load(f)
        merge(m,data)

  with open(file, "r") as f:
    for line in f.readlines():

      match = re.search(r'@skip', line)
      if match:
        m['skip'] = True

      match = re.search(r'@flag (.*)',line)
      if match:
        m['flags'] += [match.group(1)]

      match = re.search(r'@expect (.*)',line)
      if match:
        m['expect'] = match.group(1)

  if not m['skip'] and not 'expect' in m:
    print red("WARNING: @expect MISSING IN %s" % file)
    m['expect'] = 'verified'

  return m
  
print "Running regression tests..."
print

passed = failed = 0
for test in glob.glob("./**/*.c"):
  meta = metadata(test)

  if meta['skip']:
    continue

  print "{0:>20}".format(test)

  cmd = ['smackverify.py', test]
  cmd += ['--time-limit', str(meta['time-limit'])]
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
