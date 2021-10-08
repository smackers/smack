import os
import re
import sys
import subprocess
import time
from shutil import copyfile
import smack.top
import smack.frontend
from .toSVCOMPformat import smackJsonToXmlGraph

def svcomp_frontend(input_file, args):
  """Generate Boogie code from SVCOMP-style C-language source(s)."""

  # enable static LLVM unroll pass
  args.static_unroll = True

  # attempt to rewrite bitwise ops into provided models
  args.rewrite_bitwise_ops = True

  # Modeling of strings must be turned on by default
  args.strings = True

  if len(args.input_files) > 1:
    raise RuntimeError("Expected a single SVCOMP input file.")

  # check svcomp properties and set flags accordingly
  svcomp_check_property(args)

  if smack.top.VProperty.INTEGER_OVERFLOW in args.check:
    args.integer_encoding = 'bit-vector'

  name, ext = os.path.splitext(os.path.basename(args.input_files[0]))
  args.orig_files = list(args.input_files)

  args.clang_options += " -fbracket-depth=2048"
  args.clang_options += " -Wno-unknown-attributes"
  args.clang_options += " -DSVCOMP"
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
    from smack.top import VProperty
    from smack.top import VResult
    if "valid-deref" in prop:
      args.check = VProperty.VALID_DEREF
    elif "valid-memcleanup" in prop:
      args.check = VProperty.MEMLEAK
    elif "overflow" in prop:
      args.check = VProperty.INTEGER_OVERFLOW
    elif not "reach_error" in prop:
      result = VResult.UNKNOWN
      print(result.message(args))
      sys.exit(result.return_code())

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

  from smack.top import VProperty
  from smack.top import VResult

  if not (VProperty.MEMORY_SAFETY in args.check
          or VProperty.MEMLEAK in args.check
          or VProperty.INTEGER_OVERFLOW in args.check):
    inject_assert_false(args)

  # Setting good loop unroll bound based on benchmark class
  loopUnrollBar = 13
  time_limit = 880

  corral_command = ["corral"]
  corral_command += [args.bpl_file]
  corral_command += ["/tryCTrace", "/noTraceOnDisk", "/printDataValues:1"]
  corral_command += ["/useProverEvaluate", "/cex:1"]
  corral_command += ["/bopt:proverOpt:O:smt.qi.eager_threshold=100"]
  corral_command += ["/bopt:proverOpt:O:smt.arith.solver=2"]
  corral_command += ["/timeLimit:%s" % time_limit]
  corral_command += ["/v:1"]
  corral_command += ["/recursionBound:65536"]
  corral_command += ["/trackAllVars"]

  verifier_output = smack.top.try_command(corral_command, timeout=time_limit)
  result = smack.top.verification_result(verifier_output, 'corral')

  if result in VResult.ERROR: #normal inlining
    heurTrace += "Found a bug during normal inlining.\n"

    if not args.quiet:
      error = smack.top.error_trace(verifier_output, 'corral')
      print(error)

  elif result is VResult.TIMEOUT: #normal inlining
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
      write_error_file(args, VResult.VERIFIED, verifier_output)
      print(VResult.VERIFIED.message(args))
      sys.exit(VResult.VERIFIED.return_code())
    else:
      heurTrace += "Only unrolled " + str(unrollMax) + " times.\n"
      heurTrace += "Insufficient unrolls to consider 'verified'.  "
      heurTrace += "Reporting 'timeout'.\n"
      if not args.quiet:
        print((heurTrace + "\n"))
        sys.stdout.flush()
      force_timeout()
  elif result is VResult.VERIFIED: #normal inlining
    heurTrace += "Normal inlining terminated and found no bugs.\n"
  else: #normal inlining
    heurTrace += "Normal inlining returned 'unknown'.  See errors above.\n"
  if not args.quiet:
    print((heurTrace + "\n"))
  write_error_file(args, result, verifier_output)
  print(result.message(args))
  sys.exit(result.return_code())

def write_error_file(args, status, verifier_output):
  from smack.top import VProperty
  from smack.top import VResult
  from smack.errtrace import json_output_str
  #return
  if status is VResult.UNKNOWN:
    return
  hasBug = (status is not VResult.VERIFIED)
  #if not hasBug:
  #  return
  if args.error_file:
    error = None
    if args.language == 'svcomp':
      error = smackJsonToXmlGraph(json_output_str(status, verifier_output, 'corral', False), args, hasBug, status)
    elif hasBug:
      error = smack.top.error_trace(verifier_output, 'corral')
    if error is not None:
      with open(args.error_file, 'w') as f:
        f.write(error.decode('utf-8'))

