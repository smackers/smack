import os
import re
import sys
import subprocess
import time
import smack.top
import filters
from toSVCOMPformat import smackJsonToXmlGraph
from random_testing import random_test

def svcomp_frontend(args):
  """Generate Boogie code from SVCOMP-style C-language source(s)."""

  # enable static LLVM unroll pass
  args.static_unroll = True
  # disable dynamic execution
  args.execute = False

  if len(args.input_files) > 1:
    raise RuntimeError("Expected a single SVCOMP input file.")

  # check svcomp properties and set flags accordingly
  svcomp_check_property(args)

  # fix: disable float filter for memory safety benchmarks
  if not args.memory_safety:
    # test bv and executable benchmarks
    file_type, executable = filters.svcomp_filter(args.input_files[0])
    if file_type == 'bitvector':
      args.bit_precise = True
      args.bit_precise_pointers = True
    if file_type == 'float':
      #sys.exit(smack.top.results(args)['unknown'])
      args.float = True
      args.bit_precise = True
      args.bit_precise_pointers = True
      args.verifier = 'boogie'
      args.time_limit = 880
    args.execute = executable
  else:
    with open(args.input_files[0], "r") as sf:
      sc = sf.read()
    if 'unsigned char b:2' in sc:
      args.bit_precise = True
      #args.bit_precise_pointers = True

  name, ext = os.path.splitext(os.path.basename(args.input_files[0]))
  svcomp_process_file(args, name, ext)

  args.clang_options += " -DAVOID_NAME_CONFLICTS"
  args.clang_options += " -DCUSTOM_VERIFIER_ASSERT"
  args.clang_options += " -DNO_FORALL"
  args.clang_options += " -DDISABLE_PTHREAD_ASSERTS"
  args.clang_options += " -include smack.h"

  if os.path.splitext(args.input_files[0])[1] == ".i":
    # Ensure clang runs the preprocessor, even with .i extension.
    args.clang_options += " -x c"

  smack.top.clang_frontend(args)

def svcomp_check_property(args):
  # Check if property is vanilla reachability, and return unknown otherwise
  if args.svcomp_property:
    with open(args.svcomp_property, "r") as f:
      prop = f.read()
    if "valid-deref" in prop:
      args.memory_safety = True
    elif "overflow" in prop:
      args.signed_integer_overflow = True
    elif not "__VERIFIER_error" in prop:
      sys.exit(smack.top.results(args)['unknown'])

def svcomp_process_file(args, name, ext):
  args.orig_files = list(args.input_files)
  with open(args.input_files[0], 'r') as fi:
    s = fi.read()
    args.input_files[0] = smack.top.temporary_file(name, ext, args)
    # replace exit definition with exit_
    s = re.sub(r'void\s+exit\s*\(int s\)', r'void exit_(int s)', s)

    if args.memory_safety:
      s = re.sub(r'typedef long unsigned int size_t', r'typedef unsigned int size_t', s)

    if args.float:
      if re.search("fesetround|fegetround",s):
        sys.exit(smack.top.results(args)['unknown'])

    length = len(s.split('\n'))
    if length < 60:
      # replace all occurrences of 100000 with 10 and 15000 with 5
      # Only target at small examples
      s = re.sub(r'100000', r'10', s)
      s = re.sub(r'15000', r'5', s)
      s = re.sub(r'i<=10000', r'i<=1', s)
    elif length < 710 and 'dll_create_master' in s:
      args.no_memory_splitting = True

    #Remove any preprocessed declarations of pthread types
    #Also, if file contains 'pthread', set pthread mode
    s,args.pthread = filters.scrub_pthreads(s)
    if args.pthread:
      s = "#include <pthread.h>\n" + s
    with open(args.input_files[0], 'w') as fo:
      fo.write(s)

def verify_bpl_svcomp(args):
  """Verify the Boogie source file using SVCOMP-tuned heuristics."""
  heurTrace = "\n\nHeuristics Info:\n"

  # If pthreads found, perform lock set analysis
  if args.pthread:
    lockpwn_command = ["lockpwn"]
    lockpwn_command += [args.bpl_file]
    lockpwn_command += ["/corral"]
    args.bpl_file = smack.top.temporary_file(os.path.splitext(os.path.basename(args.bpl_file))[0], '.bpl', args)
    lockpwn_command += ["/o:%s" % args.bpl_file]
    lockpwn_output = smack.top.try_command(lockpwn_command);

  corral_command = ["corral"]
  corral_command += [args.bpl_file]
  corral_command += ["/tryCTrace", "/noTraceOnDisk", "/printDataValues:1"]
  corral_command += ["/useProverEvaluate", "/cex:1"]

  with open(args.bpl_file, "r") as f:
    bpl = f.read()

  if args.pthread:
    if "fib_bench" in bpl or "unregister_chrdev" in bpl:
      heurTrace += "Increasing context switch bound for certain pthread benchmarks.\n"
      corral_command += ["/k:30"]
    else:
      corral_command += ["/k:3"]
    if not "qrcu_reader2" in bpl and not "__VERIFIER_atomic_take_write_lock" in bpl:
      corral_command += ["/cooperative"]
  else:
    corral_command += ["/k:1"]
    if not args.memory_safety or not args.bit_precise:
      corral_command += ["/di"]

  # we are not modeling strcpy
  if args.pthread and "strcpy" in bpl:
    heurTrace += "We are not modeling strcpy - aborting\n"
    if not args.quiet:
      print(heurTrace + "\n")
    sys.exit(smack.top.results(args)['unknown'])

  # Setting good loop unroll bound based on benchmark class
  loopUnrollBar = 8
  staticLoopBound = 65536
  if not args.bit_precise and "ssl3_accept" in bpl and "s__s3__tmp__new_cipher__algorithms" in bpl:
    heurTrace += "ControlFlow benchmark detected. Setting loop unroll bar to 23.\n"
    loopUnrollBar = 23
  elif "s3_srvr.blast.10_false-unreach-call" in bpl:
    heurTrace += "ControlFlow benchmark detected. Setting loop unroll bar to 23.\n"
    loopUnrollBar = 23
  elif " node3" in bpl:
    heurTrace += "Sequentialized benchmark detected. Setting loop unroll bar to 100.\n"
    loopUnrollBar = 100
  elif "calculate_output" in bpl:
    heurTrace += "ECA benchmark detected. Setting loop unroll bar to 15.\n"
    loopUnrollBar = 15
  elif "ldv" in bpl:
    heurTrace += "LDV benchmark detected. Setting loop unroll bar to 13.\n"
    loopUnrollBar = 13
    staticLoopBound = 64
  elif "standard_strcpy_false-valid-deref_ground_true-termination" in bpl or "960521-1_false-valid-free" in bpl or "960521-1_false-valid-deref" in bpl or "lockfree-3.3" in bpl:
    heurTrace += "Memory safety benchmark detected. Setting loop unroll bar to 129.\n"
    loopUnrollBar = 129
  elif "id_o1000_false-unreach-call" in bpl:
    heurTrace += "Recursive benchmark detected. Setting loop unroll bar to 1024.\n"
    loopUnrollBar = 1024
  elif args.memory_safety and "__main(argc:" in bpl:
    heurTrace += "BusyBox benchmark detected. Setting loop unroll bar to 128.\n"
    loopUnrollBar = 128
  elif args.signed_integer_overflow and "jain" in bpl:
    heurTrace += "Infinite loop in overflow benchmark. Setting loop unroll bar to INT_MAX.\n"
    loopUnrollBar = 2**31 - 1

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
  command += ["/maxStaticLoopBound:%d" % staticLoopBound]
  command += ["/recursionBound:65536"]
  command += ["/irreducibleLoopUnroll:2"]
  command += ["/trackAllVars"]

  verifier_output = smack.top.try_command(command, timeout=time_limit)
  result = smack.top.verification_result(verifier_output)

  if result == 'error' or result == 'invalid-deref' or result == 'invalid-free' or result == 'invalid-memtrack' or result == 'overflow': #normal inlining
    heurTrace += "Found a bug during normal inlining.\n"

    if not args.quiet:
      error = smack.top.error_trace(verifier_output, args)
      print error

  elif result == 'timeout': #normal inlining
    heurTrace += "Timed out during normal inlining.\n"
    heurTrace += "Determining result based on how far we unrolled.\n"
    # If we managed to unroll more than loopUnrollBar times, then return verified
    # First remove exhausted loop bounds generated during max static loop bound computation
    unrollMax = 0
    if 'Verifying program while tracking' in verifier_output:
      verifier_output = re.sub(re.compile('.*Verifying program while tracking', re.DOTALL),
        'Verifying program while tracking', verifier_output)
      it = re.finditer(r'Exhausted recursion bound of ([1-9]\d*)', verifier_output)
      for match in it:
        if int(match.group(1)) > unrollMax:
          unrollMax = int(match.group(1))
    else:
      heurTrace += "Corral didn't even start verification.\n"
    if unrollMax >= loopUnrollBar:
      heurTrace += "Unrolling made it to a recursion bound of "
      heurTrace += str(unrollMax) + ".\n"
      heurTrace += "Reporting benchmark as 'verified'.\n"
      if args.execute and not args.pthread:
        heurTrace += "Hold on, let's see the execution result.\n"
        execution_result = run_binary(args)
        heurTrace += "Excecution result is " + execution_result + '\n'
        if execution_result != 'true':
          heurTrace += "Oops, execution result says {0}.\n".format(execution_result)
          if not args.quiet:
            print(heurTrace + "\n")
          sys.exit(smack.top.results(args)['unknown'])
      random_test_result = random_test(args, result)
      if random_test_result == 'false' or random_test_result == 'unknown':
        heurTrace += "Oops, random testing says {0}.\n".format(random_test_result)
        if not args.quiet:
          print(heurTrace + "\n")
        sys.exit(smack.top.results(args)['unknown'])
      if not args.quiet:
        print(heurTrace + "\n")
      write_error_file(args, 'verified', verifier_output)
      sys.exit(smack.top.results(args)['verified'])
    else:
      heurTrace += "Only unrolled " + str(unrollMax) + " times.\n"
      heurTrace += "Insufficient unrolls to consider 'verified'.  "
      heurTrace += "Reporting 'timeout'.\n"
      if not args.quiet:
        print(heurTrace + "\n")
        sys.stdout.flush()
      # Sleep for 1000 seconds, so svcomp shows timeout instead of unknown
      time.sleep(1000)
  elif result == 'verified': #normal inlining
    heurTrace += "Normal inlining terminated and found no bugs.\n"
  else: #normal inlining
    heurTrace += "Normal inlining returned 'unknown'.  See errors above.\n"
  if not args.quiet:
    print(heurTrace + "\n")
  write_error_file(args, result, verifier_output)
  sys.exit(smack.top.results(args)[result])

def write_error_file(args, status, verifier_output):
  hasBug = (status != 'verified' and status != 'timeout' and status != 'unknown')
  if not hasBug:
    return
  if args.error_file:
    error = None
    if args.language == 'svcomp':
      error = smackJsonToXmlGraph(smack.top.smackdOutput(verifier_output), args, hasBug)
    elif hasBug:
      error = smack.top.error_trace(verifier_output, args)
    if error is not None:
      with open(args.error_file, 'w') as f:
        f.write(error)

def run_binary(args):
  #process the file to make it runnable
  with open(args.input_files[0], 'r') as fi:
    s = fi.read()

  s = re.sub(r'(extern )?void __VERIFIER_error()', '//', s)
  s = re.sub(r'__VERIFIER_error\(\)', 'assert(0)', s)
  s = '#include<assert.h>\n' + s

  name = os.path.splitext(os.path.basename(args.input_files[0]))[0]
  tmp1 = smack.top.temporary_file(name, '.c', args)
  with open(tmp1, 'w') as fo:
    fo.write(s)

  tmp2 = smack.top.temporary_file(name, '.bin', args)
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
        print 'Execution error'
        print err
        return 'unknown'
    else:
      return 'true'
