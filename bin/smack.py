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
import tempfile
from threading import Timer
from toSVCOMPformat import *
from token_replace import *

VERSION = '1.5.1'
temporary_files = []

def rewriteIExtensionToC(args):
  """ For svcomp mode, if file extension ends in .i, we need to make a copy as
a .c file.  If we don't, clang treats the file as if preprocessing has already 
occurred (and so doesn't run preprocessor)"""
  #TODO check if there is a clang switch that causes clang to run preprocessor
  #     even if file extension is .i
  fileName = os.path.splitext(os.path.basename(args.input_file))[0]
  newFileName = os.path.join(args.bcFolder, fileName) + '.original.c'
  shutil.copyfile(args.input_file, newFileName)
  return newFileName

def replacer(args):
  inputFileName = args.input_file
  errorWitnessFileName = args.error_witness
  outputFileName = args.bpl_file

  fileName, fileExtension = os.path.splitext(os.path.basename(inputFileName))
  with open(inputFileName, "r") as inputFile:
    inputStr = inputFile.read()

  """ If error witness flag is enabled, do tokenizing """
  """ First get rid of these patterns which cause errors """
  inputStr = re.sub(r'#line .*', '', inputStr)
  inputStr = re.sub(r'# \d+.*', '', inputStr)
  inputStr = re.sub(r'#pragma .*','',inputStr)
  inputStr = beforeTokenReplace(inputStr)
  """ Save valid tokens a tmp file in the folder containing bc files """
  """ since tokenizer binary only accepts file as argument """
  beforeTokenizedName = os.path.join(args.bcFolder, fileName) + '.tmp'
  with open(beforeTokenizedName, 'w') as replacedFile:
    replacedFile.write(inputStr)
  tokenizedName = os.path.join(args.bcFolder, fileName) + '.tokenized.c'
  cmd = ['tokenizer', beforeTokenizedName]

  try:
    with open(tokenizedName, 'w') as tokenizedFile:
      proc = subprocess.Popen(cmd, preexec_fn=os.setsid, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
      output = proc.communicate()[0]
      output = afterTokenReplace(output)
      tokenizedFile.write(output)
      rc = proc.returncode
      proc = None
    if rc:
      raise RuntimeError("%s returned non-zero." % cmd[0])
  except (RuntimeError, OSError) as err:
    if output:
      print >> sys.stderr, output
    sys.exit("Error invoking command:\n%s\n%s" % (" ".join(cmd), err))
  finally:
    if proc: os.killpg(os.getpgid(proc.pid), signal.SIGKILL)

  temporary_files.append(beforeTokenizedName)
  args.input_file = tokenizedName
  return args

def frontends():
  """A dictionary of front-ends per file extension."""
  return {
    '.i': clang_frontend,
    '.c': clang_frontend,
    '.cc': clang_frontend,
    '.cpp': clang_frontend,
    '.bc': empty_frontend,
    '.ll': empty_frontend,
  }

def results():
  """A dictionary of the result output messages."""
  return {
    'verified': 'SMACK found no errors.',
    'error': 'SMACK found an error.',
    'timeout': 'SMACK timed out.',
    'unknown': 'SMACK result is unknown.'
  }

def inlined_procedures():
  return [
    '$alloc',
    '$free',
    '$memset',
    '$memcpy',
  ]

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

  parser.add_argument('--version', action='version',
    version='SMACK version ' + VERSION)

  noise_group = parser.add_mutually_exclusive_group()

  noise_group.add_argument('-q', '--quiet', action='store_true', default=False,
    help='enable quiet output')

  noise_group.add_argument('-v', '--verbose', action='store_true', default=False,
    help='enable verbose output')

  noise_group.add_argument('-d', '--debug', action="store_true", default=False,
    help='enable debugging output')

  parser.add_argument('-tx', '--no-verify', action="store_true", default=False,
    help='perform only translation, without verification.')

  parser.add_argument('-tr', '--trace-file', metavar='FILE', default=None,
    type=str, help='save error trace to FILE')

  frontend_group = parser.add_argument_group('front-end options')

  frontend_group.add_argument('-bc', '--bc-file', metavar='FILE', default=None,
    type=str, help='save (intermediate) bitcode to FILE')

  frontend_group.add_argument('--clang-options', metavar='OPTIONS', default='',
    help='additional compiler arguments (e.g., --clang-options="-w -g")')

  translate_group = parser.add_argument_group('translation options')

  translate_group.add_argument('-bpl', '--bpl-file', metavar='FILE', default=None,
    type=str, help='save (intermediate) Boogie code to FILE')

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

  svcomp_group = parser.add_argument_group('svcomp options')

  svcomp_group.add_argument('--svcomp', action="store_true", default=False,
    help='enter svcomp mode')

  svcomp_group.add_argument('--syntax-check', action="store_true", default=False,
    help='do syntax check on generated boogie file only')

  svcomp_group.add_argument('--error-witness', metavar='FILE', default=None, type=str, 
    help='save error witness to FILE')

  args = parser.parse_args()

  if not args.bc_file:
    args.bc_file = temporary_file('a', '.bc', args)
    
  if not args.bpl_file:
    args.bpl_file = 'a.bpl' if args.no_verify else temporary_file('a', '.bpl', args)

  # TODO are we (still) using this?
  # with open(args.input_file, 'r') as f:
  #   for line in f.readlines():
  #     m = re.match('.*SMACK-OPTIONS:[ ]+(.*)$', line)
  #     if m:
  #       return args = parser.parse_args(m.group(1).split() + sys.argv[1:])

  if args.svcomp:
    args.bcFolder = os.path.relpath(os.path.abspath(os.path.dirname(args.bc_file)))
    args.bplFolder = os.path.relpath(os.path.abspath(os.path.dirname(args.bpl_file)))
    if args.error_witness:
      args.errorWitnessFolder = os.path.relpath(os.path.abspath(os.path.dirname(args.error_witness)))
    if os.path.splitext(args.input_file)[1] == ".i":
      args.input_file = rewriteIExtensionToC(args)
    if args.error_witness:
      args = replacer(args)

  return args

def temporary_file(prefix, extension, args):
  f, name = tempfile.mkstemp(extension, prefix + '-', os.getcwd(), True)
  os.close(f)
  temporary_files.append(name)
  return name

def timeout_killer(proc, timed_out):
  if not timed_out[0]:
    timed_out[0] = True
    os.killpg(os.getpgid(proc.pid), signal.SIGKILL)

def try_command(cmd):
  output = ""
  proc = None
  timer = None
  try:
    proc = subprocess.Popen(cmd, preexec_fn=os.setsid, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    timed_out = [False]
    timer = Timer(args.time_limit, timeout_killer, [proc, timed_out])
    timer.start()

    if args.verbose or args.debug:
      output = ""
      print "Running %s" % " ".join(cmd)
      while proc.poll() is None:
        line = proc.stdout.readline()
        if line:
          sys.stdout.write(line)
          output += line
        else:
          break

    output += proc.communicate()[0]
    timer.cancel()
    rc = proc.returncode
    proc = None
    if timed_out[0]:
      return output + ("\n%s timed out." % cmd[0])
    elif rc:
      raise RuntimeError("%s returned non-zero." % cmd[0])
    else:
      return output

  except (RuntimeError, OSError) as err:
    if output:
      print >> sys.stderr, output
    sys.exit("Error invoking command:\n%s\n%s" % (" ".join(cmd), err))

  finally:
    if timer: timer.cancel()
    if proc: os.killpg(os.getpgid(proc.pid), signal.SIGKILL)

def frontend(args):
  """Generate the LLVM bitcode file."""
  return frontends()[os.path.splitext(args.input_file)[1]](args)

def empty_frontend(args):
  """Generate the LLVM bitcode file by copying the input file."""
  shutil.copy(args.input_file, args.bc_file)

def clang_frontend(args):
  """Generate an LLVM bitcode file from C-language source(s)."""

  smack_root = os.path.dirname(os.path.dirname(os.path.abspath(sys.argv[0])))
  smack_headers = os.path.join(smack_root, 'share', 'smack', 'include')
  smack_lib = os.path.join(smack_root, 'share', 'smack', 'lib')
  smack_bc = temporary_file('smack', '.bc', args)
  smack_svcomp_bc = temporary_file('smack-svcomp', '.bc', args)

  compile_command = ['clang', '-c', '-emit-llvm', '-O0', '-g', '-gcolumn-info']
  compile_command += args.clang_options.split()
  compile_command += ['-I' + smack_headers, '-include' + ('smack-svcomp.h' if args.svcomp else 'smack.h')]
  compile_command += ['-DMEMORY_MODEL_' + args.mem_mod.upper().replace('-','_')]
  if args.svcomp:
    compile_command += ['-DSVCOMP']
  link_command = ['llvm-link']

  try_command(compile_command + [os.path.join(smack_lib, 'smack.c'), '-o', smack_bc])
  if args.svcomp:
    try_command(compile_command + [os.path.join(smack_lib, 'smack-svcomp.c'), '-o', smack_svcomp_bc])
  try_command(compile_command + [args.input_file, '-o', args.bc_file])
  try_command((lambda t, x, y, l1, l2: l1 + ([x, y] if t else [x,]) + l2) (args.svcomp, smack_bc, smack_svcomp_bc, link_command + [args.bc_file,], ['-o', args.bc_file]))

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
  if name in args.entry_points:
    return "{:entrypoint}"
  elif re.match("|".join(inlined_procedures()).replace("$","\$"), name):
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

def verification_result(verifier_output):
  if re.search(r'[1-9]\d* time out|Z3 ran out of resources|timed out', verifier_output):
    return 'timeout'
  elif re.search(r'[1-9]\d* verified, 0 errors?|no bugs', verifier_output):
    return 'verified'
  elif re.search(r'0 verified, [1-9]\d* errors?|can fail', verifier_output):
    return 'error'
  else:
    return 'unknown'

def verify_bpl(args):
  """Verify the Boogie source file with a back-end verifier."""

  if args.verifier == 'boogie':
    command = ["boogie"]
    command += [args.bpl_file]
    command += ["/nologo"]
    command += ["/timeLimit:%s" % args.time_limit]
    command += ["/errorLimit:%s" % args.max_violations]
    command += ["/loopUnroll:%d" % args.unroll]

  elif args.verifier == 'corral':
    command = ["corral"]
    command += [args.bpl_file]
    command += ["/tryCTrace", "/noTraceOnDisk", "/printDataValues:1"]
    command += ["/useProverEvaluate", "/newStratifiedInlining"]
    command += ["/timeLimit:%s" % args.time_limit]
    command += ["/cex:%s" % args.max_violations]
    command += ["/maxStaticLoopBound:%d" % args.loop_limit]
    command += ["/recursionBound:%d" % args.unroll]

  else:
    # Duality!
    command = ["corral", args.bpl_file]
    command += ["/tryCTrace", "/useDuality", "/recursionBound:10000"]

  if args.bit_precise:
    x = "bopt:" if args.verifier != 'boogie' else ""
    command += ["/%sproverOpt:OPTIMIZE_FOR_BV=true" % x]
    command += ["/%sz3opt:smt.relevancy=0" % x]
    command += ["/%sz3opt:smt.bv.enable_int2bv=true" % x]
    command += ["/%sboolControlVC" % x]

  if args.verifier_options:
    command += args.verifier_options.split()

  verifier_output = try_command(command)
  result = verification_result(verifier_output)

  if args.smackd:
    print smackdOutput(verifier_output)



  else:
    if args.error_witness and result == 'error':
      witnessStr = smackJsonToXmlGraph(smackdOutput(verifier_output))
      with open(args.error_witness, 'w') as witnessFile:
        witnessFile.write(witnessStr)

    print results()[result]
    if result == 'error':
      trace = error_trace(verifier_output, args)
      if args.trace_file:
        with open(args.trace_file, 'w') as f:
          f.write(trace)
      if not args.quiet:
        print trace

def error_step(step):
  FILENAME = '[\w#$~%.\/-]*'
  step = re.match("(\s*)(%s)\((\d+),\d+\): (.*)" % FILENAME, step)
  if step:
    if re.match('.*[.]bpl$', step.group(2)):
      line_no = int(step.group(3))
      message = step.group(4)
      if re.match('.*\$bb\d+.*', message):
        message = ""
      with open(step.group(2)) as f:
        for line in f.read().splitlines(True)[line_no:line_no+10]:
          src = re.match(".*{:sourceloc \"(%s)\", (\d+), (\d+)}" % FILENAME, line)
          if src:
            return "%s%s(%s,%s): %s" % (step.group(1), src.group(1), src.group(2), src.group(3), message)
    else:
      return step.group(0)
  else:
    return None

def error_trace(verifier_output, args):
  trace = ""
  for line in verifier_output.splitlines(True):
    step = error_step(line)
    if step:
      m = re.match('(.*): [Ee]rror [A-Z0-9]+: (.*)', step)
      if m:
        trace += "%s: %s\nExecution trace:\n" % (m.group(1), m.group(2))
      else:
        trace += ('' if step[0] == ' ' else '    ') + step + "\n"

  return trace

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
      traceAssumeMatch = re.match('(' + FILENAME + ')\((\d+),(\d+)\): Trace: Thread=(\d+)  (\((\W*\w+\W*=\W*\w+\W*)\))$', traceLine)
      errorMatch = re.match('(' + FILENAME + ')\((\d+),(\d+)\): (error .*)$', traceLine)
      if traceMatch:
        filename = str(traceMatch.group(1))
        lineno = int(traceMatch.group(2))
        colno = int(traceMatch.group(3))
        threadid = int(traceMatch.group(4))
        desc = str(traceMatch.group(6))
        assm = ''
        if traceAssumeMatch:
          assm = str(traceAssumeMatch.group(6))
        trace = { 'threadid': threadid, 
                  'file': filename, 
                  'line': lineno, 
                  'column': colno, 
                  'description': '' if desc == 'None' else desc, 
                  'assumption': assm }
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
  return json_string

if __name__ == '__main__':
  try:
    args = arguments()

    if not args.quiet:
      print "SMACK program verifier version %s" % VERSION

    frontend(args)
    llvm_to_bpl(args)
    annotate_bpl(args)

    if args.no_verify:
      if not args.quiet:
        print "SMACK generated %s" % args.bpl_file
    else:
      verify_bpl(args)

  except KeyboardInterrupt:
    if not args.quiet:
      print >> sys.stderr, "SMACK aborted by keyboard interrupt."

  finally:
    for f in temporary_files:
      if os.path.isfile(f):
        os.unlink(f)
