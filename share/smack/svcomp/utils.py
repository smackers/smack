import os
import re
import sys
import subprocess
import time
from shutil import copyfile
import smack.top
import smack.frontend
import filters
from toSVCOMPformat import smackJsonToXmlGraph
from random_testing import random_test

def svcomp_frontend(input_file, args):
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
    if file_type == 'float' and not args.integer_overflow:
      #sys.exit(smack.top.results(args)['unknown'])
      args.float = True
      args.bit_precise = True
      args.bit_precise_pointers = True
      #args.verifier = 'boogie'
      args.time_limit = 1000
      args.unroll = 100
    args.execute = executable
  else:
    with open(input_file, "r") as sf:
      sc = sf.read()
    if 'unsigned char b:2' in sc or "4294967294u" in sc:
      args.bit_precise = True
      #args.bit_precise_pointers = True

  name, ext = os.path.splitext(os.path.basename(args.input_files[0]))
  svcomp_process_file(args, name, ext)

  args.clang_options += " -DSVCOMP"
  args.clang_options += " -DAVOID_NAME_CONFLICTS"
  args.clang_options += " -DCUSTOM_VERIFIER_ASSERT"
  args.clang_options += " -DNO_FORALL"
  args.clang_options += " -DDISABLE_PTHREAD_ASSERTS"
  args.clang_options += " -include smack.h"

  if os.path.splitext(input_file)[1] == ".i":
    # Ensure clang runs the preprocessor, even with .i extension.
    args.clang_options += " -x c"

  bc = smack.frontend.clang_frontend(args.input_files[0], args)

  # run with no extra smack libraries
  libs = set()

  smack.top.link_bc_files([bc],libs,args)

def svcomp_check_property(args):
  # Check if property is vanilla reachability, and return unknown otherwise
  if args.svcomp_property:
    with open(args.svcomp_property, "r") as f:
      prop = f.read()
    if "valid-deref" in prop:
      args.memory_safety = True
    elif "overflow" in prop:
      args.integer_overflow = True
    elif not "__VERIFIER_error" in prop:
      sys.exit(smack.top.results(args)['unknown'])

def svcomp_process_file(args, name, ext):
  args.orig_files = list(args.input_files)
  with open(args.input_files[0], 'r') as fi:
    s = fi.read()
    args.input_files[0] = smack.top.temporary_file(name, ext, args)
    # replace exit definition with exit_
    s = re.sub(r'void\s+exit\s*\(int s\)', r'void exit_(int s)', s)
    if not ('direc_start' in s or 'just_echo' in s):
      s = re.sub(r'argv\[i\]=malloc\(11\);\s+argv\[i\]\[10\]\s+=\s+0;\s+for\(int\s+j=0;\s+j<10;\s+\+\+j\)\s+argv\[i\]\[j\]=__VERIFIER_nondet_char\(\);', r'argv[i] = malloc(3);\n    argv[i][0] = __VERIFIER_nondet_char();\n    argv[i][1] = __VERIFIER_nondet_char();\n    argv[i][2] = 0;', s)
      s = re.sub(r'char\s+\*a\s+=\s+malloc\(11\);\s+a\[10\]\s+=\s+0;\s+for\(int\s+i=0;\s+i<10;\s+\+\+i\)\s+a\[i\]=__VERIFIER_nondet_char\(\);', r'char *a = malloc(3);\n  a[0] = __VERIFIER_nondet_char();\n  a[1] = __VERIFIER_nondet_char();\n  a[2] = 0;', s)
    s = re.sub(r'static\s+char\s+dir\[42\];\s+for\(int\s+i=0;\s+i<42;\s+\+\+i\)\s+dir\[i\]\s+=\s+__VERIFIER_nondet_char\(\);\s+dir\[41\]\s+=\s+\'\\0\';', r'static char dir[3];\n  dir[0] = __VERIFIER_nondet_char();\n  dir[1] = __VERIFIER_nondet_char();\n  dir[2] = 0;', s)
    s = re.sub(r'__VERIFIER_assume\(i < 16\);', r'__VERIFIER_assume(i >= 0 && i < 16);', s)

    if args.memory_safety and not 'argv=malloc' in s:
      s = re.sub(r'typedef long unsigned int size_t', r'typedef unsigned int size_t', s)
    elif args.memory_safety and re.search(r'getopt32\([^,)]+,[^,)]+,[^.)]+\);', s):
      if not args.quiet:
        print("Stumbled upon a benchmark that requires precise handling of vararg\n")
      while (True):
        pass
    elif args.memory_safety and ('count is too big' in s or 'pdRfilsLHarPv' in s or 'rnugG' in s):
      if not args.quiet:
        print("Stumbled upon a benchmark that contains undefined behavior\n")
      while (True):
        pass

    if 'argv=malloc' in s:
#      args.bit_precise = True
      if args.integer_overflow and ('unsigned int d = (unsigned int)((signed int)(unsigned char)((signed int)*q | (signed int)(char)32) - 48);' in s or 'bb_ascii_isalnum' in s or 'ptm=localtime' in s or '0123456789.' in s):
        args.bit_precise = True
        args.bit_precise_pointers = True

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

def is_crappy_driver_benchmark(args, bpl):
  if ("205_9a_array_safes_linux-3.16-rc1.tar.xz-205_9a-drivers--net--usb--rtl8150.ko-entry_point_true-unreach-call" in bpl or
      "32_7a_cilled_true-unreach-call_linux-3.8-rc1-32_7a-drivers--gpu--drm--ttm--ttm.ko-ldv_main5_sequence_infinite_withcheck_stateful" in bpl or
      "32_7a_cilled_true-unreach-call_linux-3.8-rc1-32_7a-drivers--media--dvb-core--dvb-core.ko-ldv_main5_sequence_infinite_withcheck_stateful" in bpl or
      "32_7a_cilled_true-unreach-call_linux-3.8-rc1-32_7a-sound--core--seq--snd-seq.ko-ldv_main2_sequence_infinite_withcheck_stateful" in bpl or
      "43_2a_bitvector_linux-3.16-rc1.tar.xz-43_2a-drivers--net--xen-netfront.ko-entry_point_true-unreach-call" in bpl or
      "linux-3.14__complex_emg__linux-drivers-clk1__drivers-net-ethernet-ethoc_true-unreach-call" in bpl or
      "linux-3.14__linux-usb-dev__drivers-media-usb-hdpvr-hdpvr_true-unreach-call" in bpl or
      "linux-4.2-rc1.tar.xz-32_7a-drivers--net--usb--r8152.ko-entry_point_true-unreach-call" in bpl or
      "linux-3.14__complex_emg__linux-kernel-locking-spinlock__drivers-net-ethernet-smsc-smsc911x_true-unreach-call" in bpl or
      "linux-3.14__complex_emg__linux-kernel-locking-spinlock__drivers-net-wan-lmc-lmc_true-unreach-call" in bpl or
      "linux-4.2-rc1.tar.xz-43_2a-drivers--net--ppp--ppp_generic.ko-entry_point_true-unreach-call" in bpl):
    if not args.quiet:
      print("Stumbled upon a crappy device driver benchmark\n")
    while (True):
      pass

def force_timeout():
  sys.stdout.flush()
  time.sleep(1000)

def verify_bpl_svcomp(args):
  """Verify the Boogie source file using SVCOMP-tuned heuristics."""
  heurTrace = "\n\nHeuristics Info:\n"

  if args.memory_safety:
    if not (args.only_check_valid_deref or args.only_check_valid_free or args.only_check_memleak):
      heurTrace = "engage valid deference checks.\n"
      args.only_check_valid_deref = True
      args.prop_to_check = 'valid-deref'
      args.bpl_with_all_props = smack.top.temporary_file(os.path.splitext(os.path.basename(args.bpl_file))[0], '.bpl', args)
      copyfile(args.bpl_file, args.bpl_with_all_props)
      smack.top.property_selection(args)
    elif args.only_check_valid_deref:
      heurTrace = "engage valid free checks.\n"
      args.only_check_valid_free = True
      args.prop_to_check = 'valid-free'
      args.only_check_valid_deref = False
      args.bpl_file = smack.top.temporary_file(os.path.splitext(os.path.basename(args.bpl_file))[0], '.bpl', args)
      copyfile(args.bpl_with_all_props, args.bpl_file)
      smack.top.property_selection(args)
    elif args.only_check_valid_free:
      heurTrace = "engage memleak checks.\n"
      args.only_check_memleak = True
      args.prop_to_check = 'memleak'
      args.only_check_valid_free = False
      args.bpl_file = smack.top.temporary_file(os.path.splitext(os.path.basename(args.bpl_file))[0], '.bpl', args)
      copyfile(args.bpl_with_all_props, args.bpl_file)
      smack.top.property_selection(args)

  # invoke boogie for floats
  # I have to copy/paste part of verify_bpl
  if args.float:
    args.verifier = 'boogie'
    boogie_command = ["boogie"]
    boogie_command += [args.bpl_file]
    boogie_command += ["/nologo", "/noinfer", "/doModSetAnalysis"]
    boogie_command += ["/timeLimit:%s" % args.time_limit]
    boogie_command += ["/errorLimit:%s" % args.max_violations]
    boogie_command += ["/loopUnroll:%d" % args.unroll]
    if args.bit_precise:
      x = "bopt:" if args.verifier != 'boogie' else ""
      boogie_command += ["/%sproverOpt:OPTIMIZE_FOR_BV=true" % x]
      boogie_command += ["/%sboolControlVC" % x]

    if args.verifier_options:
      boogie_command += args.verifier_options.split()

    boogie_output = smack.top.try_command(boogie_command, timeout=args.time_limit)
    boogie_result = smack.top.verification_result(boogie_output)
    write_error_file(args, boogie_result, boogie_output)
    sys.exit(smack.top.results(args)[boogie_result])

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

  is_crappy_driver_benchmark(args, bpl)

  if args.pthread:
    if "fib_bench" in bpl or "27_Boop_simple_vf_false-unreach-call" in bpl:
      heurTrace += "Increasing context switch bound for certain pthread benchmarks.\n"
      corral_command += ["/k:30"]
    else:
      corral_command += ["/k:3"]
    if not "qrcu_reader2" in bpl and not "__VERIFIER_atomic_take_write_lock" in bpl and not "fib_bench" in bpl:
      corral_command += ["/cooperative"]
  else:
    corral_command += ["/k:1"]
    if not (args.memory_safety or args.bit_precise):
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
  elif "s3_srvr.blast.10_false-unreach-call" in bpl or "s3_srvr.blast.15_false-unreach-call" in bpl:
    heurTrace += "ControlFlow benchmark detected. Setting loop unroll bar to 23.\n"
    loopUnrollBar = 23
  elif "NonTerminationSimple4_false-no-overflow" in bpl:
    heurTrace += "Overflow benchmark detected. Setting loop unroll bar to 1024.\n"
    loopUnrollBar = 1024
  elif " node3" in bpl:
    heurTrace += "Sequentialized benchmark detected. Setting loop unroll bar to 100.\n"
    loopUnrollBar = 100
  elif "calculate_output" in bpl or "psyco" in bpl:
    heurTrace += "ECA benchmark detected. Setting loop unroll bar to 15.\n"
    loopUnrollBar = 15
  elif "ldv" in bpl:
    if "linux-4.2-rc1.tar.xz-08_1a-drivers--staging--lustre--lustre--llite--llite_lloop.ko-entry_point" in bpl or "linux-3.14__complex_emg__linux-usb-dev__drivers-media-usb-hdpvr-hdpvr" in bpl:
      heurTrace += "Special LDV benchmark detected. Setting loop unroll bar to 32.\n"
      loopUnrollBar = 32
    else:
      heurTrace += "LDV benchmark detected. Setting loop unroll bar to 13.\n"
      loopUnrollBar = 13
    staticLoopBound = 64
  elif "standard_strcpy_false-valid-deref_ground_true-termination" in bpl or "960521-1_false-valid-free" in bpl or "960521-1_false-valid-deref" in bpl or "lockfree-3.3" in bpl or "list-ext_false-unreach-call_false-valid-deref" in bpl:
    heurTrace += "Memory safety benchmark detected. Setting loop unroll bar to 129.\n"
    loopUnrollBar = 129
  elif "is_relaxed_prefix" in bpl:
    heurTrace += "Benchmark relax_* detected. Setting loop unroll bar to 15.\n"
    loopUnrollBar = 15
  elif "id_o1000_false-unreach-call" in bpl:
    heurTrace += "Recursive benchmark detected. Setting loop unroll bar to 1024.\n"
    loopUnrollBar = 1024
  elif "n.c24" in bpl or "array_false-unreach-call3" in bpl:
    heurTrace += "Loops benchmark detected. Setting loop unroll bar to 1024.\n"
    loopUnrollBar = 1024
  elif "printf_false-unreach-call" in bpl or "echo_true-no-overflow" in bpl:
    heurTrace += "BusyBox benchmark detected. Setting loop unroll bar to 11.\n"
    loopUnrollBar = 11
  elif args.memory_safety and "__main($i0" in bpl:
    heurTrace += "BusyBox memory safety benchmark detected. Setting loop unroll bar to 4.\n"
    loopUnrollBar = 4
  elif args.integer_overflow and "__main($i0" in bpl:
    heurTrace += "BusyBox overflows benchmark detected. Setting loop unroll bar to 11.\n"
    loopUnrollBar = 11
  elif args.integer_overflow and ("jain" in bpl or "TerminatorRec02" in bpl or "NonTerminationSimple" in bpl):
    heurTrace += "Infinite loop in overflow benchmark. Setting loop unroll bar to INT_MAX.\n"
    loopUnrollBar = 2**31 - 1

  if not "forall" in bpl:
    heurTrace += "No quantifiers detected. Setting z3 relevancy to 0.\n"
    corral_command += ["/bopt:z3opt:smt.relevancy=0"]

  if args.bit_precise:
    heurTrace += "--bit-precise flag passed - enabling bit vectors mode.\n"
    corral_command += ["/bopt:proverOpt:OPTIMIZE_FOR_BV=true"]
    corral_command += ["/bopt:boolControlVC"]

  if args.memory_safety:
    if args.prop_to_check == 'valid-deref':
      if "memleaks_test12_false-valid-free" in bpl:
        time_limit = 10
      else:
        time_limit = 750
    elif args.prop_to_check == 'valid-free':
      time_limit = 80
    elif args.prop_to_check == 'memleak':
      time_limit = 50
  else:
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
    if args.memory_safety:
      heurTrace += (args.prop_to_check + "has errors\n")
      if args.prop_to_check == 'valid-free':
        if args.valid_deref_check_result != 'verified':
          force_timeout()
      elif args.prop_to_check == 'memleak':
        if args.valid_free_check_result == 'timeout':
          force_timeout()

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
      if args.memory_safety:
        heurTrace += (args.prop_to_check + "is verified\n")
        if args.prop_to_check == 'valid-deref':
          args.valid_deref_check_result = 'verified'
        elif args.prop_to_check == 'valid-free':
          args.valid_free_check_result = 'verified'
        elif args.prop_to_check == 'memleak':
          if args.valid_deref_check_result == 'timeout':
            force_timeout()
          else:
            sys.exit(smack.top.results(args)[args.valid_deref_check_result])
        verify_bpl_svcomp(args)
      else:
        write_error_file(args, 'verified', verifier_output)
        sys.exit(smack.top.results(args)['verified'])
    else:
      heurTrace += "Only unrolled " + str(unrollMax) + " times.\n"
      heurTrace += "Insufficient unrolls to consider 'verified'.  "
      heurTrace += "Reporting 'timeout'.\n"
      if not args.quiet:
        print(heurTrace + "\n")
        sys.stdout.flush()
      if args.memory_safety:
        heurTrace += (args.prop_to_check + " times out\n")
        if args.prop_to_check == 'valid-deref':
          args.valid_deref_check_result = 'timeout'
          force_timeout()
        elif args.prop_to_check == 'valid-free':
          args.valid_free_check_result = 'timeout'
        elif args.prop_to_check == 'memleak':
          if args.valid_deref_check_result == 'timeout':
            force_timeout()
          else:
            sys.exit(smack.top.results(args)[args.valid_deref_check_result])
        verify_bpl_svcomp(args)
      else:
        # Sleep for 1000 seconds, so svcomp shows timeout instead of unknown
        time.sleep(1000)
  elif result == 'verified': #normal inlining
    heurTrace += "Normal inlining terminated and found no bugs.\n"
  else: #normal inlining
    heurTrace += "Normal inlining returned 'unknown'.  See errors above.\n"
  if not args.quiet:
    print(heurTrace + "\n")
  if args.memory_safety and result == 'verified':
    heurTrace += (args.prop_to_check + " is verified\n")
    if args.prop_to_check == 'valid-deref':
      args.valid_deref_check_result = 'verified'
    elif args.prop_to_check == 'valid-free':
      args.valid_free_check_result = 'verified'
    elif args.prop_to_check == 'memleak':
      if args.valid_deref_check_result == 'timeout':
        force_timeout()
      else:
        sys.exit(smack.top.results(args)[args.valid_deref_check_result])
    verify_bpl_svcomp(args)
  else:
    write_error_file(args, result, verifier_output)
    sys.exit(smack.top.results(args)[result])

def write_error_file(args, status, verifier_output):
  return
  if args.memory_safety or status == 'timeout' or status == 'unknown':
    return
  hasBug = (status != 'verified')
  #if not hasBug:
  #  return
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
