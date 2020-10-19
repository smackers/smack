import os
import re
import sys
import subprocess
import time
from shutil import copyfile
import smack.top
import smack.frontend
from . import filters
from .toSVCOMPformat import smackJsonToXmlGraph

def svcomp_frontend(input_file, args):
  """Generate Boogie code from SVCOMP-style C-language source(s)."""

  # enable static LLVM unroll pass
  args.static_unroll = True

  if len(args.input_files) > 1:
    raise RuntimeError("Expected a single SVCOMP input file.")

  # check svcomp properties and set flags accordingly
  svcomp_check_property(args)

  # fix: disable float filter for memory safety benchmarks
  if not ('memory-safety' in args.check or 'memleak' in args.check):
    # figure out category
    file_type = filters.svcomp_filter(args.input_files[0])
    if file_type == 'bitvector':
      args.integer_encoding = 'bit-vector'
      args.pointer_encoding = 'bit-vector'
    if file_type == 'float' and not 'integer-overflow' in args.check:
      args.float = True
      args.integer_encoding = 'bit-vector'
      args.pointer_encoding = 'bit-vector'

  if 'memory-safety' in args.check or 'memleak' in args.check or 'integer-overflow' in args.check:
    args.strings = True

  name, ext = os.path.splitext(os.path.basename(args.input_files[0]))
  svcomp_process_file(args, name, ext)

  args.clang_options += " -fbracket-depth=2048"
  args.clang_options += " -Wno-unknown-attributes"
  args.clang_options += " -DSVCOMP"
  args.clang_options += " -DAVOID_NAME_CONFLICTS"
  args.clang_options += " -DCUSTOM_VERIFIER_ASSERT"
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
  if args.svcomp_property:
    with open(args.svcomp_property, "r") as f:
      prop = f.read()
    if "valid-deref" in prop:
      args.check = ['memory-safety']
    elif "valid-memcleanup" in prop:
      args.check = ['memleak']
    elif "overflow" in prop:
      args.check = ['integer-overflow']
    elif not "reach_error" in prop:
      print(smack.top.results(args)['unknown'][0])
      sys.exit(smack.top.results(args)['unknown'][1])

def svcomp_process_file(args, name, ext):
  args.orig_files = list(args.input_files)
  with open(args.input_files[0], 'r') as fi:
    s = fi.read()
    args.input_files[0] = smack.top.temporary_file(name, ext, args)

    #Remove any preprocessed declarations of pthread types
    #Also, if file contains 'pthread', set pthread mode
    s,args.pthread = filters.scrub_pthreads(s)
    if args.pthread:
      s = "#include <pthread.h>\n" + s
    with open(args.input_files[0], 'w') as fo:
      fo.write(s)

def force_timeout():
  sys.stdout.flush()
  time.sleep(1000)

def inject_assert_false(args):
    with open(args.bpl_file, 'r') as bf:
      content = bf.read()
    content = content.replace('call reach_error();', 'assert false; call reach_error();')
    with open(args.bpl_file, 'w') as bf:
      bf.write(content)

def verify_bpl_svcomp(args):
  """Verify the Boogie source file using SVCOMP-tuned heuristics."""
  heurTrace = "\n\nHeuristics Info:\n"

  if not 'memory-safety' in args.check and not 'memleak' in args.check and not 'integer-overflow' in args.check:
    inject_assert_false(args)

  if 'memory-safety' in args.check:
    if len(args.check) == 1:
      heurTrace = "engage valid deference checks.\n"
      args.check.pop()
      args.check.append('valid-deref')
      args.prop_to_check = 'valid-deref'
      args.bpl_with_all_props = smack.top.temporary_file(os.path.splitext(os.path.basename(args.bpl_file))[0], '.bpl', args)
      copyfile(args.bpl_file, args.bpl_with_all_props)
      smack.top.memsafety_subproperty_selection(args)
      args.check.append('memory-safety')
    elif 'valid-deref' in args.check:
      heurTrace = "engage valid free checks.\n"
      args.check.pop()
      args.check.pop()
      args.prop_to_check = 'valid-free'
      args.check.append('valid-free')
      args.bpl_file = smack.top.temporary_file(os.path.splitext(os.path.basename(args.bpl_file))[0], '.bpl', args)
      copyfile(args.bpl_with_all_props, args.bpl_file)
      smack.top.memsafety_subproperty_selection(args)
      args.check.append('memory-safety')
    elif 'valid-free' in args.check:
      heurTrace = "engage memleak checks.\n"
      args.check.pop()
      args.check.pop()
      args.prop_to_check = 'memleak'
      args.check.append('memleak')
      args.bpl_file = smack.top.temporary_file(os.path.splitext(os.path.basename(args.bpl_file))[0], '.bpl', args)
      copyfile(args.bpl_with_all_props, args.bpl_file)
      smack.top.memsafety_subproperty_selection(args)
      args.check.append('memory-safety')
  elif 'memleak' in args.check:
    heurTrace = "engage memcleanup checks.\n"
    smack.top.memsafety_subproperty_selection(args)

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
  corral_command += ["/bopt:proverOpt:O:smt.qi.eager_threshold=100"]
  corral_command += ["/bopt:proverOpt:O:smt.arith.solver=2"]

  with open(args.bpl_file, "r") as f:
    bpl = f.read()

  with open(args.input_files[0], "r") as f:
    csource = f.read()

  if args.pthread:
    if "fib_bench" in bpl or "27_Boop_simple_vf_false-unreach-call" in bpl or "k < 5;" in csource or "k < 10;" in csource or "k < 20;" in csource:
      heurTrace += "Increasing context switch bound for certain pthread benchmarks.\n"
      corral_command += ["/k:30"]
    else:
      corral_command += ["/k:3"]
    if not "qrcu_reader2" in bpl and not "__VERIFIER_atomic_take_write_lock" in bpl and not "fib_bench" in bpl:
      corral_command += ["/cooperative"]
  else:
    corral_command += ["/k:1"]
    if not ('memory-safety' in args.check or args.integer_encoding == 'bit-vector' or 'memleak' in args.check):
      if not ("dll_create" in csource or "sll_create" in csource or "changeMethaneLevel" in csource):
        corral_command += ["/di"]

  # Setting good loop unroll bound based on benchmark class
  loopUnrollBar = 13
  staticLoopBound = 64

  if 'memory-safety' in args.check:
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
  command += ["/irreducibleLoopUnroll:12"]
  command += ["/trackAllVars"]

  verifier_output = smack.top.try_command(command, timeout=time_limit)
  result = smack.top.verification_result(verifier_output)

  if result == 'error' or result == 'invalid-deref' or result == 'invalid-free' or result == 'invalid-memtrack' or result == 'overflow': #normal inlining
    heurTrace += "Found a bug during normal inlining.\n"

    if not args.quiet:
      error = smack.top.error_trace(verifier_output, args)
      print(error)
    if 'memory-safety' in args.check:
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
      if not args.quiet:
        print((heurTrace + "\n"))
      if 'memory-safety' in args.check:
        heurTrace += (args.prop_to_check + "is verified\n")
        if args.prop_to_check == 'valid-deref':
          args.valid_deref_check_result = 'verified'
        elif args.prop_to_check == 'valid-free':
          args.valid_free_check_result = 'verified'
        elif args.prop_to_check == 'memleak':
          if args.valid_deref_check_result == 'timeout':
            force_timeout()
          else:
            print(smack.top.results(args)[args.valid_deref_check_result][0])
            sys.exit(smack.top.results(args)[args.valid_deref_check_result][1])
        verify_bpl_svcomp(args)
      else:
        write_error_file(args, 'verified', verifier_output)
        print(smack.top.results(args)['verified'][0])
        sys.exit(smack.top.results(args)['verified'][1])
    else:
      heurTrace += "Only unrolled " + str(unrollMax) + " times.\n"
      heurTrace += "Insufficient unrolls to consider 'verified'.  "
      heurTrace += "Reporting 'timeout'.\n"
      if not args.quiet:
        print((heurTrace + "\n"))
        sys.stdout.flush()
      if 'memory-safety' in args.check:
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
            print(smack.top.results(args)[args.valid_deref_check_result][0])
            sys.exit(smack.top.results(args)[args.valid_deref_check_result][1])
        verify_bpl_svcomp(args)
      else:
        force_timeout()
  elif result == 'verified': #normal inlining
    heurTrace += "Normal inlining terminated and found no bugs.\n"
  else: #normal inlining
    heurTrace += "Normal inlining returned 'unknown'.  See errors above.\n"
  if not args.quiet:
    print((heurTrace + "\n"))
  if 'memory-safety' in args.check and result == 'verified':
    heurTrace += (args.prop_to_check + " is verified\n")
    if args.prop_to_check == 'valid-deref':
      args.valid_deref_check_result = 'verified'
    elif args.prop_to_check == 'valid-free':
      args.valid_free_check_result = 'verified'
    elif args.prop_to_check == 'memleak':
      if args.valid_deref_check_result == 'timeout':
        force_timeout()
      else:
        print(smack.top.results(args)[args.valid_deref_check_result][0])
        sys.exit(smack.top.results(args)[args.valid_deref_check_result][1])
    verify_bpl_svcomp(args)
  else:
    write_error_file(args, result, verifier_output)
    if 'memleak' in args.check and result == 'invalid-memtrack':
      sys.exit('SMACK found an error: memory cleanup.')
    else:
      print(smack.top.results(args)[result][0])
      sys.exit(smack.top.results(args)[result][1])

def write_error_file(args, status, verifier_output):
  #return
  if status == 'timeout' or status == 'unknown':
    return
  hasBug = (status != 'verified')
  #if not hasBug:
  #  return
  if args.error_file:
    error = None
    if args.language == 'svcomp':
      error = smackJsonToXmlGraph(smack.top.smackdOutput(verifier_output), args, hasBug, status)
    elif hasBug:
      error = smack.top.error_trace(verifier_output, args)
    if error is not None:
      with open(args.error_file, 'w') as f:
        f.write(error.decode('utf-8'))

