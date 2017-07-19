import json
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

  print "Attempting to replay error trace."

  missing_definitions = detect_missing_definitions(args.bc_file)
  if '__SMACK_code' in missing_definitions:
    print "warning: inline Boogie code found; replay may fail"

  arguments, return_values = extract_values(verifier_output)

  with open(args.replay_harness, 'w') as f:
    f.write(harness(arguments, return_values, missing_definitions))
  print "Generated replay harness:", args.replay_harness

  stubs_bc = temporary_file('stubs', '.bc', args)
  try_command(['clang', '-c', '-emit-llvm', '-o', stubs_bc, args.replay_harness])
  try_command(['clang', '-Wl,-e,_smack_replay_main', '-o', args.replay_exe_file, args.bc_file, stubs_bc])
  print "Generated replay executable:", args.replay_exe_file

  try:
    if 'error reached!' in try_command(["./" + args.replay_exe_file]):
      print "Error-trace replay successful."
      return True

    else:
      print "Error-trace replay failed."

  except Exception as err:
    print "Error-trace replay caught", err.message

  return False


def detect_missing_definitions(bc_file):
  missing = []
  try:
    try_command(['clang', bc_file])
  except Exception as err:
    for line in err.message.split("\n"):
      m = re.search(r'\"_(.*)\", referenced from:', line) or re.search(r'undefined reference to `(.*)\'', line)
      if m:
        missing.append(m.group(1))
  return missing


def extract(line):
  match = re.search(r'.*\((smack:.*) = (.*)\).*', line)
  return match and [match.group(1), match.group(2)]


def parse_value(val):
  return json.loads(re.sub(r"[() ]", "", val))


def extract_values(trace):
  arguments = {}
  return_values = {}

  for key, val in filter(lambda x: x, map(extract, trace.split('\n'))):
    val = parse_value(val)

    if 'smack:entry:' in key:
      _, _, fn = key.split(':')
      arguments[fn] = []

    elif 'smack:arg:' in key:
      _, _, fn, arg = key.split(':')
      if not fn in arguments:
        raise Exception("expected entry point key smack:entry:%s" % fn)
      arguments[fn].append(val)

    elif 'smack:ext:' in key:
      _, _, fn = key.split(':')
      if not fn in return_values:
        return_values[fn] = []
      return_values[fn].append(val)

    else:
      print "warning: unexpected key %s" % key

  return arguments, return_values

def entrypoint_parameters(arguments):
  declarations = []
  parameters = []
  count = 0
  for arg in arguments:
    if type(arg) is dict:
      name = "ary%d" % count
      base = int(parameters.pop())
      if len(arg) > 1:
        # NOTE this is an unreliable approximation of the array size taken from
        # the biggest index mentioned in the error model. The generated program
        # will happily segfault if any accesses outside of this approximate
        # bound are made.
        biggest = int(max(arg, key=arg.get))
      else:
        # NOTE this is an arbitrary default value
        biggest = 999999
      size = biggest - base + 1
      default = int(arg['*'])
      declarations.append("void* %s[%d];" % (name, size))
      declarations.append("memset(%s,%d,%d);" % (name, default, size))
      for idx, val in arg.items():
        if idx == '*':
          pass
        else:
          # NOTE this offset calculation assumes that the array is an array of
          # 64-bit values, e.g., 64-bit pointers. While this is fine for the
          # usual `char** argv` parameter to `main` on 64-bit architectures,
          # this would not work for `argv` on 32-bit architectures, nor arrays
          # of 8-bit, 16-bit, or 32-bit integers as parameters (on any
          # architecture). Ultimately this type information ought to be passed
          # down from the llvm-to-bpl translation.
          offset = (int(idx) - base) / 8
          declarations.append("%s[%d] = %d;" % (name, offset, int(val)))
      parameters.append(name)
      count += 1
    else:
      parameters.append(str(arg))
  return declarations, parameters

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
  if (!b) {
    printf("error reached!\\n");
    exit(0);
  }
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
      print "warning: unknown return value for %s" % fn
      code.append("""// stub for function %(fn)s
void %(fn)s() {
  return;
}
""" % {'fn': fn})

  if len(arguments) > 1:
    print "warning: multiple entrypoint argument annotations found"

  elif len(arguments) < 1:
    print "warning: no entrypoint argument annotations found"

  for fn, args in arguments.items():
    declarations, parameters = entrypoint_parameters(args)
    code.append("""// entry point wrapper
int _smack_replay_main() {
  %(decls)s
  %(fn)s(%(vals)s);
  return 0;
}
int smack_replay_main() {
  %(decls)s
  %(fn)s(%(vals)s);
  return 0;
}
""" % {'decls': "\n  ".join(declarations), 'fn': fn, 'vals': ", ".join(parameters)})

  return "\n".join(code)
