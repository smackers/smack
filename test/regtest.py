#! /usr/bin/env python

import yaml
import argparse
from os import path
import subprocess
import re
import glob
import time
import sys

OVERRIDE_FIELDS = ['verifiers', 'memory', 'time-limit', 'skip']
APPEND_FIELDS = ['flags']

def red(text):
  return '\033[0;31m' + text + '\033[0m'
  
def green(text):
  return '\033[0;32m' + text + '\033[0m'

def get_result(output):
  if re.search(r'[1-9]\d* time out|Z3 ran out of resources|z3 timed out|Corral timed out', output):
    return 'timeout'
  elif re.search(r'[1-9]\d* verified, 0 errors?|no bugs', output):
    return 'verified'
  elif re.search(r'0 verified, [1-9]\d* errors?|can fail', output):
    return 'error'
  else:
    return 'unknown'

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
        m['flags'] += [match.group(1).strip()]

      match = re.search(r'@expect (.*)',line)
      if match:
        m['expect'] = match.group(1).strip()

  if not m['skip'] and not 'expect' in m:
    print red("WARNING: @expect MISSING IN %s" % file)
    m['expect'] = 'verified'

  return m
  
parser = argparse.ArgumentParser()
parser.add_argument("--exhaustive", help="be exhaustive", action="store_true")
args = parser.parse_args()

print "Running regression tests..."
print

passed = failed = timeouts = unknowns = 0

try:
  for test in glob.glob("./**/*.c"):
    meta = metadata(test)

    if meta['skip'] == True:
      continue

    if meta['skip'] != False and not args.exhaustive:
      continue

    print "{0:>20}".format(test)
    sys.stdout.flush()

    cmd = ['smackverify.py', test]
    cmd += ['--time-limit', str(meta['time-limit'])]
    cmd += ['-o', path.splitext(test)[0] + '.bpl']
    cmd += meta['flags']

    for memory in meta['memory'][:100 if args.exhaustive else 1]:
      cmd += ['--mem-mod=' + memory]

      for verifier in meta['verifiers'][:100 if args.exhaustive else 1]:
        cmd += ['--verifier=' + verifier]

        print "{0:>20} {1:>10}    :".format(memory, verifier),

        try:
          t0 = time.time()
          p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
          out, err  = p.communicate()
          elapsed = time.time() - t0

        except OSError:
          print >> sys.stderr
          sys.exit("Error executing command:\n%s" % " ".join(cmd))

        result = get_result(out+err)

        if result == meta['expect']:
          print green('PASSED '),
          passed += 1

        elif result == 'timeout':
          print red('TIMEOUT'),
          timeouts += 1

        elif result == 'unknown':
          print red('UNKNOWN'),
          unknowns += 1

        else:
          print red('FAILED '),
          failed += 1

        print '  [%.2fs]' % round(elapsed, 2)
        sys.stdout.flush()
  
except KeyboardInterrupt:
  pass

print
print ' PASSED count:', passed
print ' FAILED count:', failed

if timeouts > 0:
  print 'TIMEOUT count:', timeouts

if unknowns > 0:
  print 'UNKNOWN count:', unknowns
