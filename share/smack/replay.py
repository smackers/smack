import os
import re
import subprocess
import sys
from utils import temporary_file, try_command

def replay_error_trace(verifier_output, args):

  if args.entry_points != ['main']:
    print "Replay for entrypoints other than 'main' currently unsupported; skipping replay"
    return

  if args.verifier != 'corral':
    print "Replay for verifiers other than 'corral' currently unsupported; skipping replay"
    return

  stubs_bc = temporary_file('stubs', '.bc', args)
  missing_definitions = []

  try:
    try_command(['clang', '-o', args.replay_exe_file, args.bc_file])
  except Exception as err:
    missing_definitions = detect_missing_definitions(err[1])

  read, write = os.pipe()
  os.write(write, verifier_output)
  os.close(write)
  with open(args.replay_harness, 'w') as f:
    f.write(stub_module(aggregate_values(collect_returns(read)), missing_definitions))

  try_command(['clang', '-c', '-emit-llvm', '-o', stubs_bc, args.replay_harness])
  try_command(['clang', '-o', args.replay_exe_file, args.bc_file, stubs_bc])

  print "Generated replay harness:", args.replay_harness
  print "Generated replay executable:", args.replay_exe_file

  if try_command(["./" + args.replay_exe_file]):
    print "Error-trace replay successful."

  else:
    print "Error-trace replay failed."


def collect_returns(stream):
  return reduce(
  (lambda s, c: subprocess.Popen(c, stdin=s, stdout=subprocess.PIPE).stdout), [
    ["grep", "ext:"],
    ["sed", "s/.*ext:\(.*\) = \(.*\))/\\1,\\2/"]
  ], stream)

def detect_missing_definitions(failed_clang_output):
  missing = []
  for line in failed_clang_output.split("\n"):
    m = re.search(r'\"_(.*)\", referenced from:', line)
    if m:
      missing.append(m.group(1))
  return missing

def aggregate_values(stream):
  dict = {}
  for line in stream:
    fn, val = line.strip().split(",")
    fn = fn.replace('SMACK_nondet', 'VERIFIER_nondet')
    if not fn in dict:
        dict[fn] = []
    dict[fn].append(val)
  return dict


def stub_module(dict, missing_definitions):
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

  for fn, vals in dict.items():
    if not fn in missing_definitions:
      print "warning: using native implementation of function %s" % fn
      continue

    code.append("""// stub for function: %(fn)s
int %(fn)s$table[] = {%(vals)s};
int %(fn)s$idx = 0;

int %(fn)s() {
  return %(fn)s$table[%(fn)s$idx++];
}
""" % {'fn': fn, 'vals': ", ".join(vals)})

  return "\n".join(code)
