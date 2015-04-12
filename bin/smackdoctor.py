#!/usr/bin/env python
#
# This file is distributed under the MIT License. See LICENSE for details.
#

import os
from subprocess import Popen, PIPE
import sys
import re
import argparse
import platform

VERSION = '1.5.1'

def red(text):
  return '\033[0;31m' + text + '\033[0m'
  
def green(text):
  return '\033[0;32m' + text + '\033[0m'

def check(text, condition):
  global args
  global count
  if condition:
    if not args.quiet:
      print green("[X] " + text)
  else:
    print >> sys.stderr, red("[-] " + text)
    count += 1

def full_path(program):
  for path in os.environ['PATH'].split(os.pathsep):
    path = path.strip('"')
    exe = os.path.join(path, program)
    if os.path.isfile(exe) and os.access(exe, os.X_OK):
      return exe
  return None

def check_command(cmd):
  exe = full_path(cmd)

  check("%s is in the path" % cmd, exe is not None)
  if exe is not None:
    try:
      rc = Popen(cmd, stdout=PIPE, stderr=PIPE).wait()
    except:
      rc = None
    check("%s is executable" % cmd, rc == 1 or rc == 2)

def check_verifier(cmd):
  exe = full_path(cmd)
  var = cmd.upper()

  if exe is not None:
    check("%s is a batch script" % cmd, '#!/bin/bash' in open(exe).read())
    check("%s redirects to %s" % (cmd, var), ("$%s $@" % var) in open(exe).read())

  check("%s environment variable is set" % var, var in os.environ)
  if var in os.environ:
    check("%s invokes mono" % var, re.match(r'\Amono', os.environ[var]))
    target = os.environ[var].split()[1]
    check("%s target exists" % var, os.path.isfile(target))
    check("%s target is executable" % var, os.access(target, os.X_OK))

  check_command(cmd)

def check_headers(prefix):
  HEADERS = [
    (["share", "smack", "include", "smack.h"], "#define SMACK_H_"),
    (["share", "smack", "lib", "smack.c"], "void __SMACK_decls()")
  ]

  for (path, content) in HEADERS:
    file = os.path.join(prefix, *path)
    check("%s exists" % file, os.path.isfile(file))
    if os.path.isfile(file):
      check("%s contains %s" % (file, content), content in open(file).read())

if __name__ == '__main__':

  parser = argparse.ArgumentParser(description='Diagnose SMACK configuration issues.')
  parser.add_argument('-q', '--quiet', dest='quiet', action="store_true", default=False,
                      help='only show failed diagnostics')
  parser.add_argument('--prefix', metavar='P', dest='prefix', type=str, default='',
                      help='point to the installation prefix')
  args = parser.parse_args()
  count = 0

  if not args.quiet:
    print "Checking front-end dependencies..."
  check_command("clang")
  check_command("clang++")
  check_command("llvm-config")
  check_command("llvm-link")

  if not args.quiet:
    print "Checking back-end dependencies..."
  check_verifier("boogie")
  check_verifier("corral")

  if not args.quiet:
    print "Checking SMACK itself..."
  check_command("smack")
  check_command("llvm2bpl.py")
  check_command("smackgen.py")
  check_command("smackverify.py")

  if args.prefix is not '':
    check_headers(args.prefix)

  exit(count)
