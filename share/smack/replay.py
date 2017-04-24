import os
import re
import subprocess
import sys
from utils import temporary_file, try_command

SPECIAL_NAMES = [
  '__VERIFIER_assert',
  '__VERIFIER_assume'
]

def replay_error_trace(verifier_output, args):

  if args.verifier != 'corral':
    print "Replay for verifiers other than 'corral' currently unsupported; skipping replay"
    return

  missing_definitions = detect_missing_definitions(args.bc_file)

  read, write = os.pipe()
  os.write(write, verifier_output)
  os.close(write)
  with open(args.replay_harness, 'w') as f:
    arguments, return_values = aggregate_values(extract_values(read))
    f.write(harness(arguments, return_values, missing_definitions))

  stubs_bc = temporary_file('stubs', '.bc', args)
  try_command(['clang', '-c', '-emit-llvm', '-o', stubs_bc, args.replay_harness])
  try_command(['clang', '-Wl,-e,_smack_replay_main', '-o', args.replay_exe_file, args.bc_file, stubs_bc])

  print "Generated replay harness:", args.replay_harness
  print "Generated replay executable:", args.replay_exe_file

  if try_command(["./" + args.replay_exe_file]):
    print "Error-trace replay successful."

  else:
    print "Error-trace replay failed."


def detect_missing_definitions(bc_file):
  missing = []
  try:
    try_command(['clang', bc_file])
  except Exception as err:
    for line in err.message.split("\n"):
      m = re.search(r'\"_(.*)\", referenced from:', line)
      if m:
        missing.append(m.group(1))
  return missing


def extract_values(stream):
  return reduce(
  (lambda s, c: subprocess.Popen(c, stdin=s, stdout=subprocess.PIPE).stdout), [
    ["grep", "(smack:"],
    ["sed", "s/.*(smack:\(.*\) = \(.*\))/\\1,\\2/"]
  ], stream)


def aggregate_values(stream):
  arguments = {}
  return_values = {}

  for line in stream:
    key, val = line.strip().split(",")
    key = key.replace('SMACK_nondet', 'VERIFIER_nondet')

    if 'arg:' in key:
      _, fn, arg = key.split(':')
      if not fn in arguments:
        arguments[fn] = []
      arguments[fn].append(val)

    elif 'ext:' in key:
      _, fn = key.split(':')
      if not fn in return_values:
        return_values[fn] = []
      return_values[fn].append(val)

    else:
      print "warning: unexpected key %s" % key

  return arguments, return_values


def harness(arguments, return_values, missing_definitions):
  code = []
  code.append("""//
// This file was automatically generated from a Boogie error trace.
// It contains stubs for unspecified functions that were called in that trace.
// These stubs will return the same values they did in the error trace.
// This file can be linked with the source program to reproduce the error.
//
#include <stdlib.h>
#include <stdio.h>

void __VERIFIER_assert(int b) {
  if (!b)
    printf("error reached!\\n");
    exit(0);
}

void __VERIFIER_assume(int b) {
  if (!b) {
    printf("assumption does not hold.\\n");
    exit(-1);
  }
}
""")

  for fn in set(missing_definitions) - set(SPECIAL_NAMES):
    if fn in return_values:
      code.append("""// stub for function: %(fn)s
int %(fn)s$table[] = {%(vals)s};
int %(fn)s$idx = 0;

int %(fn)s() {
  return %(fn)s$table[%(fn)s$idx++];
}
""" % {'fn': fn, 'vals': ", ".join(return_values[fn])})

    else:
      print "warning: cannot generate stub for %s" % fn

  for fn in set(return_values) - set(missing_definitions):
    print "warning: using native implementation of function %s" % fn

  if len(arguments) > 1:
    print "warning: multiple entrypoint argument annotations found"

  elif len(arguments) < 1:
    print "warning: no entrypoint argument annotations found"

  for fn, args in arguments.items():
    code.append("""// entry point wrapper
int smack_replay_main() {
  %(fn)s(%(vals)s);
  return 0;
}
""" % {'fn': fn, 'vals': ", ".join(args)})

  return "\n".join(code)
