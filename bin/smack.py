#!/usr/bin/env python
#
# This file is distributed under the MIT License. See LICENSE for details.
#

import argparse
import io
import json
import os
import platform
import re
import shutil
import signal
import subprocess
import sys
from threading import Timer

VERSION = '1.5.1'

def frontends():
  """A dictionary of front-ends per file extension."""

  return {
    '.c': clang_frontend,
    '.cc': clang_frontend,
    '.cpp': clang_frontend,
    '.bc': empty_frontend,
    '.ll': empty_frontend,
  }

def validate_input_file(file):
  """Check whether the given input file is valid, returning a reason if not."""

  file_extension = os.path.splitext(file)[1]
  if not os.path.isfile(file):
    return ("Cannot find file %s." % file)

  elif not file_extension in frontends():
    return ("Unexpected source file extension '%s'." % file_extension)

  else:
    return None

def arguments():
  """Parse command-line arguments"""

  parser = argparse.ArgumentParser()

  parser.add_argument('input_file', metavar='input-file',
    type = lambda x: (lambda r: x if r is None else parser.error(r))(validate_input_file(x)),
    help = 'source file to be translated/verified')

  parser.add_argument('-v', '--version', action='version',
    version='SMACK version ' + VERSION)

  parser.add_argument('-d', '--debug', action="store_true", default=False,
    help='enable debugging output')

  parser.add_argument('-t', '--no-verify', action="store_true", default=False,
    help='perform only translation, without verification.')

  frontend_group = parser.add_argument_group('front-end options')

  frontend_group.add_argument('-bc', '--bc-file', metavar='FILE', default='a.bc',
    type=str, help='specify (intermediate) bitcode file [default: %(default)s]')

  frontend_group.add_argument('--clang-options', metavar='OPTIONS', default='',
    help='additional compiler arguments (e.g., --clang-options="-w -g")')

  translate_group = parser.add_argument_group('translation options')

  translate_group.add_argument('-bpl', '--bpl-file', metavar='FILE', default='a.bpl',
    type=str, help='specify (intermediate) Boogie file [default: %(default)s]')

  translate_group.add_argument('--mem-mod', choices=['no-reuse', 'no-reuse-impls', 'reuse'], default='no-reuse-impls',
    help='select memory model (no-reuse=never reallocate the same address, reuse=reallocate freed addresses) [default: %(default)s]')

  translate_group.add_argument('--bit-precise', action="store_true", default=False,
    help='enable bit precision for non-pointer values')

  translate_group.add_argument('--bit-precise-pointers', action="store_true", default=False,
    help='enable bit precision for pointer values')

  translate_group.add_argument('--no-byte-access-inference', action="store_true", default=False,
    help='disable bit-precision-related optimizations with DSA')

  translate_group.add_argument('--entry-points', metavar='PROC', nargs='+',
    default='main', help='specify top-level procedures [default: %(default)s]')

  verifier_group = parser.add_argument_group('verifier options')

  verifier_group.add_argument('--verifier',
    choices=['boogie', 'corral', 'duality'], default='corral',
    help='back-end verification engine [default: %(default)s]')

  verifier_group.add_argument('--unroll', metavar='N', default='2', type=int,
    help='loop/recursion unroll bound [default: %(default)s]')

  verifier_group.add_argument('--loop-limit', metavar='N', default='1', type=int,
    help='upper bound on minimum loop iterations [default: %(default)s]')

  verifier_group.add_argument('--verifier-options', metavar='OPTIONS', default='',
    help='additional verifier arguments (e.g., --verifier-options="/trackAllVars /staticInlining")')

  verifier_group.add_argument('--time-limit', metavar='N', default='1200', type=int,
    help='verifier time limit, in seconds [default: %(default)s]')

  verifier_group.add_argument('--max-violations', metavar='N', default='1', type=int,
    help='maximum reported assertion violations [default: %(default)s]')

  verifier_group.add_argument('--smackd', action="store_true", default=False,
    help='generate JSON-format output for SMACKd')

  args = parser.parse_args()

  # TODO are we (still) using this?
  # with open(args.input_file, 'r') as f:
  #   for line in f.readlines():
  #     m = re.match('.*SMACK-OPTIONS:[ ]+(.*)$', line)
  #     if m:
  #       return args = parser.parse_args(m.group(1).split() + sys.argv[1:])

  return args

def try_command(cmd):
  output = None
  proc = None
  timer = None
  try:
    proc = subprocess.Popen(cmd, preexec_fn=os.setsid, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    timer = Timer(args.time_limit, lambda: os.killpg(os.getpgid(proc.pid), signal.SIGKILL))
    timer.start()
    output = proc.communicate()[0]
    timer.cancel()
    if proc.returncode < 0:
      raise RuntimeError("%s timed out." % cmd[0])
    if proc.returncode > 0:
      raise RuntimeError("%s returned non-zero." % cmd[0])

  except KeyboardInterrupt:
    if timer: timer.cancel()
    if proc: os.killpg(os.getpgid(proc.pid), signal.SIGKILL)
    if output:
      print >> sys.stderr, output
    sys.exit("User aborted.")

  except (RuntimeError, OSError) as err:
    if output:
      print >> sys.stderr, output
    sys.exit("Error invoking command:\n%s\n%s" % (" ".join(cmd), err))

  return output

def empty_frontend(args):
  """Generate the LLVM bitcode file by copying the input file."""
  shutil.copy(args.input_file, args.bc_file)

def clang_frontend(args):
  """Generate an LLVM bitcode file from C-language source(s)."""

  smack_root = os.path.dirname(os.path.dirname(os.path.abspath(sys.argv[0])))
  smack_headers = os.path.join(smack_root, 'share', 'smack', 'include')
  smack_lib = os.path.join(smack_root, 'share', 'smack', 'lib', 'smack.c')

  # TODO better naming to avoid conflicts with parallel invocations
  smack_bc = 'smack.bc'

  compile_command = ['clang', '-c', '-emit-llvm', '-O0', '-g', '-gcolumn-info']
  compile_command += args.clang_options.split()
  compile_command += ['-I' + smack_headers, '-include' + 'smack.h']
  compile_command += ['-DMEMORY_MODEL_' + args.mem_mod.upper().replace('-','_')]
  link_command = ['llvm-link']

  try_command(compile_command + [smack_lib, '-o', smack_bc])
  try_command(compile_command + [args.input_file, '-o', args.bc_file])
  try_command(link_command + [args.bc_file, smack_bc, '-o', args.bc_file])

def llvm_to_bpl(args):
  """Translate the LLVM bitcode file to a Boogie source file."""

  cmd = ['smack', args.bc_file, '-bpl', args.bpl_file]
  cmd += ['-source-loc-syms']
  if args.debug: cmd += ['-debug']
  if "impls" in args.mem_mod:cmd += ['-mem-mod-impls']
  if args.bit_precise: cmd += ['-bit-precise']
  if args.bit_precise_pointers: cmd += ['-bit-precise-pointers']
  if args.no_byte_access_inference: cmd += ['-no-byte-access-inference']
  try_command(cmd)

def procedure_annotation(name, args):
  specials = re.compile('\$static_init|\$init_funcs|__SMACK_.*|assert_|assume_|__VERIFIER_.*')

  if name in args.entry_points:
    return "{:entrypoint}"

  elif args.verifier == 'boogie' and specials.match(name):
    return "{:inline 1}"

  elif args.verifier == 'boogie' and args.unroll:
    return ("{:inline %s}" % args.unroll)

  else:
    return ""

def annotate_bpl(args):
  """Annotate the Boogie source file with additional metadata."""

  proc_decl = re.compile('procedure\s+([^\s(]*)\s*\(')

  with open(args.bpl_file, 'r+') as f:
    bpl = "// generated by SMACK version %s for %s\n" % (VERSION, args.verifier)
    bpl += "// via %s\n\n" % " ".join(sys.argv)
    bpl += proc_decl.sub(lambda m: ("procedure %s %s(" % (procedure_annotation(m.group(1), args), m.group(1))), f.read())
    f.seek(0)
    f.truncate()
    f.write(bpl)

def verify_bpl(args):
  """Verify the Boogie source file with a back-end verifier."""

  if args.verifier == 'boogie':
    command = "boogie %s" % args.bpl_file
    command += " /nologo"
    command += " /timeLimit:%s" % args.time_limit
    command += " /errorLimit:%s" % args.max_violations
    command += " /loopUnroll:%d" % (args.unroll + args.loop_limit)

  elif args.verifier == 'corral':
    command = "corral %s" % args.bpl_file
    command += " /tryCTrace /noTraceOnDisk /printDataValues:1 /useProverEvaluate"
    command += " /timeLimit:%s" % args.time_limit
    command += " /cex:%s" % args.max_violations
    command += " /maxStaticLoopBound:%d" % args.loop_limit
    command += " /recursionBound:%d" % args.unroll

  else:
    # TODO why isn't unroll a parameter??
    command = "corral %s" % args.bpl_file
    command += "/tryCTrace /useDuality /recursionBound:10000"

  if args.bit_precise:
    x = "bopt:" if args.verifier != 'boogie' else ""
    command += " /%sproverOpt:OPTIMIZE_FOR_BV=true /%sz3opt:smt.relevancy=0" % (x,x)

  if args.verifier_options:
    command += " " + args.verifier_options

  verifier_output = try_command(command.split())

  # TODO clean up the following mess
  if args.verifier == 'boogie':
    if args.debug:
      print verifier_output

    sourceTrace = generateSourceErrorTrace(verifier_output, args.bpl_file)
    if sourceTrace:
      print sourceTrace
    else:
      print verifier_output

  else:
    if args.smackd:
      smackdOutput(verifier_output)
    else:
      print verifier_output

def generateSourceErrorTrace(boogieOutput, bplFileName):
  FILENAME = '[\w#$~%.\/-]+'
  LABEL = '[\w$]+'

  bplFile = open(bplFileName)
  bpl = bplFile.read()
  bplFile.close()

  if not re.search('.*{:sourceloc \"(' + FILENAME + ')\", (\d+), (\d+)}.*', bpl):
    # no debug info in bpl file
    return None

  sourceTrace = '\nSMACK verifier version ' + VERSION + '\n\n'
  for traceLine in boogieOutput.splitlines(True):
    resultMatch = re.match('Boogie .* f(inished with .*)', traceLine)
    traceMatch = re.match('([ ]+)(' + FILENAME + ')\((\d+),(\d+)\): (' + LABEL + ')', traceLine)
    errorMatch = re.match('(' + FILENAME + ')\((\d+),(\d+)\): (.*)', traceLine)
    if resultMatch:
      sourceTrace += '\nF' + resultMatch.group(1)
    elif traceMatch:
      spaces = str(traceMatch.group(1))
      filename = str(traceMatch.group(2))
      lineno = int(traceMatch.group(3))
      colno = int(traceMatch.group(4))
      label = str(traceMatch.group(5))

      for bplLine in bpl.splitlines(True)[lineno:lineno+10]:
        m = re.match('.*{:sourceloc \"(' + FILENAME + ')\", (\d+), (\d+)}.*', bplLine)
        if m:
          filename = str(m.group(1))
          lineno = int(m.group(2))
          colno = int(m.group(3))
 
          sourceTrace += spaces + filename + '(' + str(lineno) + ',' + str(colno) + ')\n'
          break
    elif errorMatch:
      filename = str(errorMatch.group(1))
      lineno = int(errorMatch.group(2))
      colno = int(errorMatch.group(3))
      message = str(errorMatch.group(4))
 
      for bplLine in bpl.splitlines(True)[lineno-2:lineno+8]:
        m = re.match('.*{:sourceloc \"(' + FILENAME + ')\", (\d+), (\d+)}.*', bplLine)
        if m:
          filename = str(m.group(1))
          lineno = int(m.group(2))
          colno = int(m.group(3))
 
          sourceTrace += filename + '(' + str(lineno) + ',' + str(colno) + '): ' + message + '\n'
          break
  return sourceTrace

def smackdOutput(corralOutput):
  FILENAME = '[\w#$~%.\/-]+'

  passedMatch = re.search('Program has no bugs', corralOutput)
  if passedMatch:
    json_data = {
      'verifier': 'corral',
      'passed?': True
    }

  else:
    traces = []
    for traceLine in corralOutput.splitlines(True):
      traceMatch = re.match('(' + FILENAME + ')\((\d+),(\d+)\): Trace: Thread=(\d+)  (\((.*)\))?$', traceLine)
      errorMatch = re.match('(' + FILENAME + ')\((\d+),(\d+)\): (error .*)$', traceLine)
      if traceMatch:
        filename = str(traceMatch.group(1))
        lineno = int(traceMatch.group(2))
        colno = int(traceMatch.group(3))
        threadid = int(traceMatch.group(4))
        desc = str(traceMatch.group(6))
        trace = { 'threadid': threadid, 'file': filename, 'line': lineno, 'column': colno, 'description': '' if desc == 'None' else desc }
        traces.append(trace)
      elif errorMatch:
        filename = str(errorMatch.group(1))
        lineno = int(errorMatch.group(2))
        colno = int(errorMatch.group(3))
        desc = str(errorMatch.group(4))
        failsAt = { 'file': filename, 'line': lineno, 'column': colno, 'description': desc }

    json_data = {
      'verifier': 'corral',
      'passed?': False,
      'failsAt': failsAt,
      'threadCount': 1,
      'traces': traces
    }
  json_string = json.dumps(json_data)
  print json_string

if __name__ == '__main__':
  args = arguments()
  frontends()[os.path.splitext(args.input_file)[1]](args)
  llvm_to_bpl(args)

  if args.no_verify:
    print "SMACK generated %s" % args.bpl_file

  else:
    annotate_bpl(args)
    verify_bpl(args)
