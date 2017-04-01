import os
import subprocess
import sys
from utils import temporary_file, try_command

STUBBABLE_FUNCTIONS = [
  "__VERIFIER_nondet"
]

def replay_error_trace(verifier_output, args):

  if args.entry_points != ['main']:
    print "Replay for entrypoints other than 'main' currently unsupported; skipping replay"
    return

  if args.verifier != 'corral':
    print "Replay for verifiers other than 'corral' currently unsupported; skipping replay"
    return

  read, write = os.pipe()
  os.write(write, verifier_output)
  os.close(write)
  with open(args.replay_harness, 'w') as f:
    f.write(stub_module(aggregate_values(collect_returns(read))))

  stubs_bc = temporary_file('stubs', '.bc', args)
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
    ["grep", "-A", "1", "-e", "RETURN from \(%s\)" % "\|".join(STUBBABLE_FUNCTIONS)],
    ["sed", "s/.*  (\(.*\))/\\1/"],
    ["cut", "-d", " ", "-f3"],
    ["grep", "-v", "-e", "--"],
    ["paste", "-d,", "-", "-"]
  ], stream)


def aggregate_values(stream):
  dict = {}
  for line in stream:
    fn, val = line.strip().split(",")
    if not fn in dict:
        dict[fn] = []
    dict[fn].append(val)
  return dict


def stub_module(dict):
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
    code.append("""// stub for function: %(fn)s
int %(fn)s$table[] = {%(vals)s};
int %(fn)s$idx = 0;

int %(fn)s() {
  return %(fn)s$table[%(fn)s$idx++];
}
""" % {'fn': fn, 'vals': ", ".join(vals)})

  return "\n".join(code)
