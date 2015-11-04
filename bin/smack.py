#!/usr/bin/env python
#
# This file is distributed under the MIT License. See LICENSE for details.
#

import argparse
import errno
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
import time
from toSVCOMPformat import *
from token_replace import *
from svcomp_filters import *

VERSION = '1.5.1'
temporary_files = []

def frontends():
  """A dictionary of front-ends per file extension."""
  return {
    'c': clang_frontend,
    'i': clang_frontend,
    'cc': clang_frontend,
    'cpp': clang_frontend,
    'json': json_compilation_database_frontend,
    'svcomp': svcomp_frontend,
    'bc': llvm_frontend,
    'll': llvm_frontend,
    'bpl': boogie_frontend,
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
    '__VERIFIER_'
  ]

def validate_input_file(file):
  """Check whether the given input file is valid, returning a reason if not."""

  file_extension = os.path.splitext(file)[1][1:]
  if not os.path.isfile(file):
    return ("Cannot find file %s." % file)

  elif not file_extension in frontends():
    return ("Unexpected source file extension '%s'." % file_extension)

  else:
    return None

def arguments():
  """Parse command-line arguments"""

  parser = argparse.ArgumentParser()

  parser.add_argument('input_files', metavar='input-files', nargs='+',
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

  parser.add_argument('-t', '--no-verify', action="store_true", default=False,
    help='perform only translation, without verification.')

  parser.add_argument('-w', '--error-file', metavar='FILE', default=None,
    type=str, help='save error trace/witness to FILE')

  frontend_group = parser.add_argument_group('front-end options')

  frontend_group.add_argument('-x', '--language', metavar='LANG',
    choices=frontends().keys(), default=None,
    help='Treat input files as having type LANG.')

  frontend_group.add_argument('-bc', '--bc-file', metavar='FILE', default=None,
    type=str, help='save (intermediate) bitcode to FILE')

  frontend_group.add_argument('--clang-options', metavar='OPTIONS', default='',
    help='additional compiler arguments (e.g., --clang-options="-w -g")')

  translate_group = parser.add_argument_group('translation options')

  translate_group.add_argument('-bpl', '--bpl-file', metavar='FILE', default=None,
    type=str, help='save (intermediate) Boogie code to FILE')

  translate_group.add_argument('--no-memory-splitting', action="store_true", default=False,
    help='disable region-based memory splitting')

  translate_group.add_argument('--mem-mod', choices=['no-reuse', 'no-reuse-impls', 'reuse'], default='no-reuse-impls',
    help='select memory model (no-reuse=never reallocate the same address, reuse=reallocate freed addresses) [default: %(default)s]')

  translate_group.add_argument('--llvm-unroll', action="store_true", default=False,
    help='enable LLVM loop unrolling pass as a preprocessing step')

  translate_group.add_argument('--pthread', action='store_true', default=False,
    help='enable support for pthread programs')

  translate_group.add_argument('--bit-precise', action="store_true", default=False,
    help='enable bit precision for non-pointer values')

  translate_group.add_argument('--bit-precise-pointers', action="store_true", default=False,
    help='enable bit precision for pointer values')

  translate_group.add_argument('--no-byte-access-inference', action="store_true", default=False,
    help='disable bit-precision-related optimizations with DSA')

  translate_group.add_argument('--entry-points', metavar='PROC', nargs='+',
    default=['main'], help='specify top-level procedures [default: %(default)s]')

  verifier_group = parser.add_argument_group('verifier options')

  verifier_group.add_argument('--verifier',
    choices=['boogie', 'corral', 'duality', 'svcomp'], default='corral',
    help='back-end verification engine [default: %(default)s]')

  verifier_group.add_argument('--unroll', metavar='N', default='2', type=int,
    help='loop/recursion unroll bound [default: %(default)s]')

  verifier_group.add_argument('--loop-limit', metavar='N', default='1', type=int,
    help='upper bound on minimum loop iterations [default: %(default)s]')

  verifier_group.add_argument('--context-bound', metavar='k', default='1', type=int,
    help='bound thread contexts in Corral to a maximum of k contexts')

  verifier_group.add_argument('--verifier-options', metavar='OPTIONS', default='',
    help='additional verifier arguments (e.g., --verifier-options="/trackAllVars /staticInlining")')

  verifier_group.add_argument('--time-limit', metavar='N', default='1200', type=int,
    help='verifier time limit, in seconds [default: %(default)s]')

  verifier_group.add_argument('--max-violations', metavar='N', default='1', type=int,
    help='maximum reported assertion violations [default: %(default)s]')

  verifier_group.add_argument('--smackd', action="store_true", default=False,
    help='generate JSON-format output for SMACKd')

  verifier_group.add_argument('--svcomp-property', metavar='FILE', default=None,
    type=str, help='load SVCOMP property to check from FILE')

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

  return args

def temporary_file(prefix, extension, args):
  f, name = tempfile.mkstemp(extension, prefix + '-', os.getcwd(), True)
  os.close(f)
  if not args.debug:
    temporary_files.append(name)
  return name

def timeout_killer(proc, timed_out):
  if not timed_out[0]:
    timed_out[0] = True
    os.killpg(os.getpgid(proc.pid), signal.SIGKILL)

def try_command(cmd, cwd=None, console=False, timeout=None):
  console = (console or args.verbose or args.debug) and not args.quiet
  filelog = args.debug
  output = ''
  proc = None
  timer = None
  try:
    if args.debug:
      print "Running %s" % " ".join(cmd)

    proc = subprocess.Popen(cmd, cwd=cwd, preexec_fn=os.setsid,
      stdout=subprocess.PIPE, stderr=subprocess.STDOUT)

    if timeout:
      timed_out = [False]
      timer = Timer(timeout, timeout_killer, [proc, timed_out])
      timer.start()

    if console:
      while True:
        line = proc.stdout.readline()
        if line:
          output += line
          print line,
        elif proc.poll() is not None:
          break
      proc.wait
    else:
      output = proc.communicate()[0]

    if timeout:
      timer.cancel()

    rc = proc.returncode
    proc = None
    if timeout and timed_out[0]:
      return output + ("\n%s timed out." % cmd[0])
    elif rc:
      raise RuntimeError("%s returned non-zero." % cmd[0])
    else:
      return output

  except (RuntimeError, OSError) as err:
    print >> sys.stderr, output
    sys.exit("Error invoking command:\n%s\n%s" % (" ".join(cmd), err))

  finally:
    if timeout and timer: timer.cancel()
    if proc: os.killpg(os.getpgid(proc.pid), signal.SIGKILL)
    if filelog:
      with open(temporary_file(cmd[0], '.log', args), 'w') as f:
        f.write(output)

def frontend(args):
  """Generate the LLVM bitcode file."""
  if args.language:
    lang = args.language
  else:
    extensions = map(lambda f: os.path.splitext(f)[1][1:], args.input_files)
    if any(map(lambda ext: ext != extensions[0], extensions)):
      raise RuntimeError("All input files must have the same file type (extension).")
    lang = extensions[0]
  return frontends()[lang](args)

def smack_root():
  return os.path.dirname(os.path.dirname(os.path.abspath(sys.argv[0])))

def smack_headers():
  return os.path.join(smack_root(), 'share', 'smack', 'include')

def smack_lib():
  return os.path.join(smack_root(), 'share', 'smack', 'lib', 'smack.c')

def default_clang_compile_command(args):
  cmd = ['clang', '-c', '-emit-llvm', '-O0', '-g', '-gcolumn-info']
  cmd += ['-I' + smack_headers()]
  cmd += args.clang_options.split()
  cmd += ['-DMEMORY_MODEL_' + args.mem_mod.upper().replace('-','_')]
  return cmd

def boogie_frontend(args):
  """Generate Boogie code by concatenating the input file(s)."""
  with open(args.bpl_file, 'w') as out:
    for src in args.input_files:
      with open(src) as f:
        out.write(f.read())

def llvm_frontend(args):
  """Generate Boogie code from LLVM bitcodes."""
  try_command(['llvm-link', '-o', args.bc_file] + args.input_files)
  llvm_to_bpl(args)

def clang_frontend(args):
  """Generate Boogie code from C-language source(s)."""

  bitcodes = []
  compile_command = default_clang_compile_command(args)
  smack_bc = temporary_file('smack', '.bc', args)
  try_command(compile_command + [smack_lib(), '-o', smack_bc])
  bitcodes.append(smack_bc)
  for c in args.input_files:
    bc = temporary_file(os.path.splitext(os.path.basename(c))[0], '.bc', args)
    try_command(compile_command + ['-o', bc, c], console=True)
    bitcodes.append(bc)
  if args.pthread:
    pthread_lib = os.path.join(smack_root(), 'share', 'smack', 'lib', 'pthread.c')
    pthread_bc = temporary_file('pthread', '.bc', args)
    spinlock_lib = os.path.join(smack_root(), 'share', 'smack', 'lib', 'spinlock.c')
    spinlock_bc = temporary_file('spinlock', '.bc', args)
    try_command(compile_command + [pthread_lib, '-o', pthread_bc])
    try_command(compile_command + [spinlock_lib, '-o', spinlock_bc])
    bitcodes.append(pthread_bc)
    bitcodes.append(spinlock_bc)
  try_command(['llvm-link', '-o', args.bc_file] + bitcodes)
  llvm_to_bpl(args)

def json_compilation_database_frontend(args):
  """Generate Boogie code from a JSON compilation database."""

  if len(args.input_files) > 1:
    raise RuntimeError("Expected a single JSON compilation database.")

  output_flags = re.compile(r"-o ([^ ]*)[.]o\b")
  optimization_flags = re.compile(r"-O[1-9]\b")
  smack_bc = temporary_file('smack', '.bc', args)

  try_command(default_clang_compile_command(args) + [smack_lib(), '-o', smack_bc])

  with open(args.input_files[0]) as f:
    for cc in json.load(f):
      if 'objects' in cc:
        # TODO what to do when there are multiple linkings?
        bit_codes = map(lambda f: re.sub('[.]o$','.bc',f), cc['objects'])
        try_command(['llvm-link', '-o', args.bc_file] + bit_codes + [smack_bc])

      else:
        out_file = output_flags.findall(cc['command'])[0] + '.bc'
        command = cc['command']
        command = output_flags.sub(r"-o \1.bc", command)
        command = optimization_flags.sub("-O0", command)
        command = command + " -emit-llvm"
        try_command(command.split(),cc['directory'], console=True)

  llvm_to_bpl(args)


def svcomp_process_file(args, name, ext):
  with open(args.input_files[0], 'r') as fi:
    s = fi.read()
    args.input_files[0] = temporary_file(name, ext, args)
    # replace exit definition with exit_
    s = re.sub(r'void\s+exit\s*\(int s\)', r'void exit_(int s)', s)
    if len(s.split('\n')) < 60:
      # replace all occurrences of 100000 with 10
      # Only target at small examples
      s = re.sub(r'100000', r'10', s)
    #Remove any preprocessed declarations of pthread types
    #Also, if file contains 'pthread', set pthread mode
    s,args.pthread = scrub_pthreads(s)
    if args.pthread:
      print("Pthread detected - setting context bound to 2")
      args.context_bound=2
      s = "#include <pthread.h>\n" + s
    #print(s)
    with open(args.input_files[0], 'w') as fo:
      fo.write(s)


def svcomp_frontend(args):
  """Generate Boogie code from SVCOMP-style C-language source(s)."""

  # enable LLVM unroll pass
  args.llvm_unroll = True

  if len(args.input_files) > 1:
    raise RuntimeError("Expected a single SVCOMP input file.")

  # test float\bv benchmarks
  file_type = svcomp_filter(args.input_files[0])[0]
  if file_type == 'bitvector': 
    args.bit_precise = True
  if file_type == 'float':
    sys.exit(results()['unknown'])
  args.execute = False
  if svcomp_filter(args.input_files[0])[1] == 'executable':
    args.execute = True

  name, ext = os.path.splitext(os.path.basename(args.input_files[0]))
  svcomp_process_file(args, name, ext)

  args.clang_options += " -DAVOID_NAME_CONFLICTS"
  args.clang_options += " -DCUSTOM_VERIFIER_ASSERT"
  args.clang_options += " -DNO_FORALL"
  args.clang_options += " -include smack.h"

  if os.path.splitext(args.input_files[0])[1] == ".i":
    # Ensure clang runs the preprocessor, even with .i extension.
    args.clang_options += " -x c"

  if args.error_file:
    # Need to check to make sure output directory exists for error trace file
    err_dir = os.path.dirname(args.error_file)
    if not os.path.exists(err_dir):
      try:
        os.makedirs(err_dir)
      except OSError as e:
        # This eliminates race condition when multiple calls to SMACK
        # try to create the same folder
        if e.errno == errno.EEXIST and os.path.isdir(err_dir):
          pass
        else:
          raise
    # SVCOMP no longer uses tokenization, so we're trying it without

    #clean = temporary_file(name, '.clean.c', args)
    #tokenized = temporary_file(name, '.tokenized.c', args)
    #
    #with open(args.input_files[0], "r") as f:
    #  cleanup = f.read()
    #cleanup = re.sub(r'#line .*|# \d+.*|#pragma .*', '', cleanup)
    #cleanup = beforeTokenReplace(cleanup)
    #with open(clean, 'w') as f:
    #  f.write(cleanup)
    #
    #output = try_command(['tokenizer', clean])
    #with open(tokenized, 'w') as f:
    #  f.write(afterTokenReplace(output))
    #
    #args.input_files[0] = tokenized

  clang_frontend(args)

def llvm_to_bpl(args):
  """Translate the LLVM bitcode file to a Boogie source file."""

  cmd = ['llvm2bpl', args.bc_file, '-bpl', args.bpl_file]
  cmd += ['-source-loc-syms']
  cmd += ['-enable-type-inference-opts']
  for ep in args.entry_points:
    cmd += ['-entry-points', ep]
  if args.debug: cmd += ['-debug']
  if "impls" in args.mem_mod:cmd += ['-mem-mod-impls']
  if args.llvm_unroll: cmd += ['-llvm-unroll']
  if args.bit_precise: cmd += ['-bit-precise']
  if args.bit_precise_pointers: cmd += ['-bit-precise-pointers']
  if args.no_byte_access_inference: cmd += ['-no-byte-access-inference']
  if args.no_memory_splitting: cmd += ['-no-memory-splitting']
  try_command(cmd, console=True)
  annotate_bpl(args)

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

def verify_bpl_svcomp(args):
  """Verify the Boogie source file using SVCOMP-tuned heuristics."""
  heurTrace = "\n\nHeuristics Info:\n"
  # Check if property is vanilla reachability, and return unknown otherwise
  if args.svcomp_property:
    with open(args.svcomp_property, "r") as f:
      prop = f.read()
    if not "__VERIFIER_error" in prop:
      heurTrace += "Unsupported svcomp property - aborting\n"
      heurTrace += "Property File:\n" + prop + "\n"
      if not args.quiet:
        print(heurTrace + "\n")
      sys.exit(results()['unknown'])

  # If pthreads found, perform lock set analysis
  if args.pthread:
    lockpwn_command = ["lockpwn"]
    lockpwn_command += [args.bpl_file]
    lockpwn_command += ["/corral"]
    lockpwn_output = try_command(lockpwn_command, timeout=time_limit);
    
  corral_command = ["corral-svcomp"]
  corral_command += [args.bpl_file]
  corral_command += ["/tryCTrace", "/noTraceOnDisk", "/printDataValues:1"]
  corral_command += ["/k:%d" % args.context_bound]
  corral_command += ["/useProverEvaluate", "/cex:1"]

  # Setting good loop unroll bound based on benchmark class
  loopUnrollBar = 8
  with open(args.bpl_file, "r") as f:
    bpl = f.read()
  if "ldv" in bpl or "calculate_output" in bpl:
    heurTrace += "ECA or LDV benchmark detected. Setting loop unroll bar to 12.\n"
    loopUnrollBar = 12
  elif "ssl3_accept" in bpl:
    heurTrace += "ControlFlow benchmark detected. Setting loop unroll bar to 25.\n"
    loopUnrollBar = 25
  if not "forall" in bpl:
    heurTrace += "No quantifiers detected. Setting z3 relevancy to 0.\n"
    corral_command += ["/bopt:z3opt:smt.relevancy=0"]

  if args.bit_precise:
    heurTrace += "--bit-precise flag passed - enabling bit vectors mode.\n"
    corral_command += ["/bopt:proverOpt:OPTIMIZE_FOR_BV=true"]
    corral_command += ["/bopt:boolControlVC"]

  time_limit = 880
  command = list(corral_command)
  command += ["/timeLimit:%s" % time_limit]
  command += ["/v:1"]
  command += ["/maxStaticLoopBound:65536"]
  command += ["/recursionBound:65536"]
  command += ["/irreducibleLoopUnroll:2"]
  command += ["/trackAllVars"]
  command += ["/di"]

  verifier_output = try_command(command, timeout=time_limit)
  result = verification_result(verifier_output)

  if result == 'error': #normal inlining
    heurTrace += "Found a bug during normal inlining.\n"
    # Generate error trace and exit
    if args.language == 'svcomp':
      error = smackJsonToXmlGraph(smackdOutput(verifier_output))
    else:
      error = error_trace(verifier_output, args)

    if args.error_file:
      with open(args.error_file, 'w') as f:
        f.write(error)

    if not args.quiet:
      print error

  elif result == 'timeout': #normal inlining
    heurTrace += "Timed out during normal inlining.\n"
    heurTrace += "Determining result based on how far we unrolled.\n"
    # If we managed to unroll more than loopUnrollBar times, then return verified
    # First remove exhausted loop bounds generated during max static loop bound computation
    verifier_output = re.sub(re.compile('.*Verifying program while tracking', re.DOTALL),
      'Verifying program while tracking', verifier_output)
    it = re.finditer(r'Exhausted recursion bound of ([1-9]\d*)', verifier_output)
    unrollMax = 0
    for match in it:
      if int(match.group(1)) > unrollMax:
        unrollMax = int(match.group(1))
    if unrollMax >= loopUnrollBar:
      heurTrace += "Unrolling made it to a recursion bound of "
      heurTrace += str(unrollMax) + ".\n"
      heurTrace += "Reporting benchmark as 'verified'.\n"
      if args.execute:
        heurTrace += "Hold on, let's see the execution result.\n"
        execution_result = run_binary(args)
        heurTrace += "Excecution result is " + execution_result + '\n'
        if execution_result == 'false':
          heurTrace += "Oops, execution result says no.\n"
          if not args.quiet:
            print(heurTrace + "\n")
          sys.exit(results()['unknown'])
      if not args.quiet:
        print(heurTrace + "\n")
      sys.exit(results()['verified'])
    else:
      heurTrace += "Only unrolled " + str(unrollMax) + " times.\n"
      heurTrace += "Insufficient unrolls to consider 'verified'.  "
      heurTrace += "Reporting 'timeout'.\n"
      if not args.quiet:
        print(heurTrace + "\n")
      # Sleep for 1000 seconds, so svcomp shows timeout instead of unknown
      time.sleep(1000)
  elif result == 'verified': #normal inlining
    heurTrace += "Normal inlining terminated and found no bugs.\n"
  else: #normal inlining
    heurTrace += "Normal inlining returned 'unknown'.  See errors above.\n"
  if not args.quiet:
    print(heurTrace + "\n")
  sys.exit(results()[result])

def run_binary(args):
  #process the file to make it runnable
  with open(args.input_files[0], 'r') as fi:
    s = fi.read()

  s = re.sub(r'(extern )?void __VERIFIER_error()', '//', s)
  s = re.sub(r'__VERIFIER_error\(\)', 'assert(0)', s)
  s = '#include<assert.h>\n' + s
 
  name = os.path.splitext(os.path.basename(args.input_files[0]))[0]
  tmp1 = temporary_file(name, '.c', args)
  with open(tmp1, 'w') as fo:
    fo.write(s)

  tmp2 = temporary_file(name, '.bin', args)
  tmp2 = tmp2.split('/')[-1]
  #compile and run 
  cmd = ['clang', tmp1, '-o', tmp2]
  #cmd += args.clang_options.split()
  #if '-m32' in args.clang_options.split():
    #cmd += ['-m32']
  

  proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)

  out, err = proc.communicate()
  rc = proc.returncode

  if rc:
    print 'Compiling error' 
    print err
    return 'unknown'
  else:
    cmd = [r'./' + tmp2]
    proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    out, err = proc.communicate()
    rc = proc.returncode
    if rc:
      if re.search(r'Assertion.*failed', err):
        return 'false'
      else:
        print 'execution error' 
        return 'unknown'
    else:
      return 'true'
    
def verify_bpl(args):
  """Verify the Boogie source file with a back-end verifier."""

  if args.verifier == 'boogie':
    command = ["boogie"]
    command += [args.bpl_file]
    command += ["/nologo", "/doModSetAnalysis"]
    command += ["/timeLimit:%s" % args.time_limit]
    command += ["/errorLimit:%s" % args.max_violations]
    command += ["/loopUnroll:%d" % args.unroll]

  elif args.verifier == 'corral':
    command = ["corral"]
    command += [args.bpl_file]
    command += ["/tryCTrace", "/noTraceOnDisk", "/printDataValues:1"]
    command += ["/k:%d" % args.context_bound]
    command += ["/useProverEvaluate"]
    command += ["/timeLimit:%s" % args.time_limit]
    command += ["/cex:%s" % args.max_violations]
    command += ["/maxStaticLoopBound:%d" % args.loop_limit]
    command += ["/recursionBound:%d" % args.unroll]

  else:
    # Duality!
    command = ["corral", args.bpl_file]
    command += ["/tryCTrace", "/noTraceOnDisk", "/useDuality", "/oldStratifiedInlining"]
    command += ["/recursionBound:1073741824", "/k:1"]

  if args.bit_precise:
    x = "bopt:" if args.verifier != 'boogie' else ""
    command += ["/%sproverOpt:OPTIMIZE_FOR_BV=true" % x]
    command += ["/%sz3opt:smt.relevancy=0" % x]
    command += ["/%sz3opt:smt.bv.enable_int2bv=true" % x]
    command += ["/%sboolControlVC" % x]

  if args.verifier_options:
    command += args.verifier_options.split()

  verifier_output = try_command(command, timeout=args.time_limit)
  result = verification_result(verifier_output)

  if args.smackd:
    print smackdOutput(verifier_output)

  elif result == 'verified':
    print results()[result]

  else:
    if result == 'error':
      if args.language == 'svcomp':
        error = smackJsonToXmlGraph(smackdOutput(verifier_output))
      else:
        error = error_trace(verifier_output, args)

      if args.error_file:
        with open(args.error_file, 'w') as f:
          f.write(error)

      if not args.quiet:
        print error

    sys.exit(results()[result])

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
    filename = ''
    lineno = 0
    colno = 0
    threadid = 0
    desc = ''
    for traceLine in corralOutput.splitlines(True):
      traceMatch = re.match('(' + FILENAME + ')\((\d+),(\d+)\): Trace: Thread=(\d+)  (\((.*)\))?$', traceLine)
      traceAssumeMatch = re.match('(' + FILENAME + ')\((\d+),(\d+)\): Trace: Thread=(\d+)  (\((\s*\w+\s*=\s*\w+\s*)\))$', traceLine)
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
          #Remove bitvector indicator from trace assumption
          assm = re.sub(r'=(\s*\d+)bv\d+', r'=\1', assm)
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

    if args.no_verify:
      if not args.quiet:
        print "SMACK generated %s" % args.bpl_file
    elif args.verifier == 'svcomp':
      verify_bpl_svcomp(args)
    else:
      verify_bpl(args)

  except KeyboardInterrupt:
    sys.exit("SMACK aborted by keyboard interrupt.")

  finally:
    for f in temporary_files:
      if os.path.isfile(f):
        os.unlink(f)
