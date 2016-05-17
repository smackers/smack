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
from svcomp.utils import svcomp_frontend
from svcomp.utils import verify_bpl_svcomp

VERSION = '1.5.2'
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

def results(args):
  """A dictionary of the result output messages."""
  return {
    'verified': 'SMACK found no errors with unroll bound %s.' % args.unroll,
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
    type=str, help='save initial LLVM bitcode to FILE')

  frontend_group.add_argument('-ll', '--ll-file', metavar='FILE', default=None,
    type=str, help='save final LLVM IR to FILE')

  frontend_group.add_argument('--clang-options', metavar='OPTIONS', default='',
    help='additional compiler arguments (e.g., --clang-options="-w -g")')

  translate_group = parser.add_argument_group('translation options')

  translate_group.add_argument('-bpl', '--bpl-file', metavar='FILE', default=None,
    type=str, help='save (intermediate) Boogie code to FILE')

  translate_group.add_argument('--no-memory-splitting', action="store_true", default=False,
    help='disable region-based memory splitting')

  translate_group.add_argument('--mem-mod', choices=['no-reuse', 'no-reuse-impls', 'reuse'], default='no-reuse-impls',
    help='select memory model (no-reuse=never reallocate the same address, reuse=reallocate freed addresses) [default: %(default)s]')

  translate_group.add_argument('--static-unroll', action="store_true", default=False,
    help='enable static LLVM loop unrolling pass as a preprocessing step')

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

  translate_group.add_argument('--memory-safety', action='store_true', default=False,
    help='enable memory safety checks')

  verifier_group = parser.add_argument_group('verifier options')

  verifier_group.add_argument('--verifier',
    choices=['boogie', 'corral', 'duality', 'svcomp'],
    help='back-end verification engine')

  verifier_group.add_argument('--unroll', metavar='N', default='1',
    type = lambda x: int(x) if int(x) > 0 else parser.error('Unroll bound has to be positive.'),
    help='loop/recursion unroll bound [default: %(default)s]')

  verifier_group.add_argument('--loop-limit', metavar='N', default='1', type=int,
    help='upper bound on minimum loop iterations [default: %(default)s]')

  verifier_group.add_argument('--context-bound', metavar='K', default='1', type=int,
    help='bound on the number of thread contexts in Corral [default: %(default)s]')

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

  if not args.verifier:
    args.verifier = 'svcomp' if args.language == 'svcomp' else 'corral'

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

def target_selection(args):
  """Determine the target architecture based on flags and source files."""
  # TODO more possible clang flags that determine the target?
  if not re.search('-target', args.clang_options):
    src = args.input_files[0]
    if os.path.splitext(src)[1] == '.bc':
      ll = temporary_file(os.path.splitext(os.path.basename(src))[0], '.ll', args)
      try_command(['llvm-dis', '-o', ll, src])
      src = ll
    if os.path.splitext(src)[1] == '.ll':
      with open(src, 'r') as f:
        for line in f:
          triple = re.findall('^target triple = "(.*)"', line)
          if len(triple) > 0:
            args.clang_options += (" -target %s" % triple[0])
            break

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
  return os.path.join(smack_root(), 'share', 'smack', 'lib')

def default_clang_compile_command(args):
  cmd = ['clang', '-c', '-emit-llvm', '-O0', '-g', '-gcolumn-info']
  cmd += ['-I' + smack_headers()]
  cmd += args.clang_options.split()
  cmd += ['-DMEMORY_MODEL_' + args.mem_mod.upper().replace('-','_')]
  return cmd

def build_libs(args):
  """Generate LLVM bitcodes for SMACK libraries."""
  bitcodes = []
  libs = ['smack.c']

  if args.pthread:
    libs += ['pthread.c', 'spinlock.c']

  for c in map(lambda c: os.path.join(smack_lib(), c), libs):
    bc = temporary_file(os.path.splitext(os.path.basename(c))[0], '.bc', args)
    try_command(default_clang_compile_command(args) + ['-o', bc, c])
    bitcodes.append(bc)

  return bitcodes

def boogie_frontend(args):
  """Generate Boogie code by concatenating the input file(s)."""
  with open(args.bpl_file, 'w') as out:
    for src in args.input_files:
      with open(src) as f:
        out.write(f.read())

def llvm_frontend(args):
  """Generate Boogie code from LLVM bitcodes."""

  bitcodes = build_libs(args) + args.input_files
  try_command(['llvm-link', '-o', args.bc_file] + bitcodes)
  llvm_to_bpl(args)

def clang_frontend(args):
  """Generate Boogie code from C-language source(s)."""

  bitcodes = build_libs(args)
  compile_command = default_clang_compile_command(args)

  for c in args.input_files:
    bc = temporary_file(os.path.splitext(os.path.basename(c))[0], '.bc', args)
    try_command(compile_command + ['-o', bc, c], console=True)
    bitcodes.append(bc)

  try_command(['llvm-link', '-o', args.bc_file] + bitcodes)
  llvm_to_bpl(args)

def json_compilation_database_frontend(args):
  """Generate Boogie code from a JSON compilation database."""

  if len(args.input_files) > 1:
    raise RuntimeError("Expected a single JSON compilation database.")

  output_flags = re.compile(r"-o ([^ ]*)[.]o\b")
  optimization_flags = re.compile(r"-O[1-9]\b")

  lib_bitcodes = build_libs(args)

  with open(args.input_files[0]) as f:
    for cc in json.load(f):
      if 'objects' in cc:
        # TODO what to do when there are multiple linkings?
        bit_codes = map(lambda f: re.sub('[.]o$','.bc',f), cc['objects'])
        try_command(['llvm-link', '-o', args.bc_file] + bit_codes + lib_bitcodes)

      else:
        out_file = output_flags.findall(cc['command'])[0] + '.bc'
        command = cc['command']
        command = output_flags.sub(r"-o \1.bc", command)
        command = optimization_flags.sub("-O0", command)
        command = command + " -emit-llvm"
        try_command(command.split(),cc['directory'], console=True)

  llvm_to_bpl(args)

def llvm_to_bpl(args):
  """Translate the LLVM bitcode file to a Boogie source file."""

  cmd = ['llvm2bpl', args.bc_file, '-bpl', args.bpl_file]
  cmd += ['-warnings']
  cmd += ['-source-loc-syms']
  cmd += ['-enable-type-inference-opts']
  for ep in args.entry_points:
    cmd += ['-entry-points', ep]
  if args.debug: cmd += ['-debug']
  if args.ll_file: cmd += ['-ll', args.ll_file]
  if "impls" in args.mem_mod:cmd += ['-mem-mod-impls']
  if args.static_unroll: cmd += ['-static-unroll']
  if args.bit_precise: cmd += ['-bit-precise']
  if args.bit_precise_pointers: cmd += ['-bit-precise-pointers']
  if args.no_byte_access_inference: cmd += ['-no-byte-access-inference']
  if args.no_memory_splitting: cmd += ['-no-memory-splitting']
  if args.memory_safety: cmd += ['-memory-safety']
  try_command(cmd, console=True)
  annotate_bpl(args)

def procedure_annotation(name, args):
  if name in args.entry_points:
    return "{:entrypoint}"
  elif re.match("|".join(inlined_procedures()).replace("$","\$"), name):
    return "{:inline 1}"
  elif args.verifier == 'boogie':
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
  elif re.search(r'\d* verified, [1-9]\d* errors?|can fail', verifier_output):
    return 'error'
  else:
    return 'unknown'

def verify_bpl(args):
  """Verify the Boogie source file with a back-end verifier."""

  if args.verifier == 'svcomp':
    verify_bpl_svcomp(args)
    return

  elif args.verifier == 'boogie':
    command = ["boogie"]
    command += [args.bpl_file]
    command += ["/nologo", "/noinfer", "/doModSetAnalysis"]
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
    print results(args)[result]

  else:
    if result == 'error':
      error = error_trace(verifier_output, args)

      if args.error_file:
        with open(args.error_file, 'w') as f:
          f.write(error)

      if not args.quiet:
        print error

    sys.exit(results(args)[result])

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

def main():
  try:
    global args
    args = arguments()

    target_selection(args)

    if not args.quiet:
      print "SMACK program verifier version %s" % VERSION

    frontend(args)

    if args.no_verify:
      if not args.quiet:
        print "SMACK generated %s" % args.bpl_file
    else:
      verify_bpl(args)

  except KeyboardInterrupt:
    sys.exit("SMACK aborted by keyboard interrupt.")

  finally:
    for f in temporary_files:
      if os.path.isfile(f):
        os.unlink(f)
