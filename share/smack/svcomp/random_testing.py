import re
import os
import smack.top
import subprocess
import sys

def random_test(args, result):
  f = args.input_files[0]

  # test if a file can be tested
  with open(f, 'r') as fi:
    s = fi.read()

  l = s.split('\n')
  if not (len(l) < 20 and len(filter(lambda x: re.search(r'=\s*__VERIFIER_nondet_uint', x), l)) == 1):
    return 'abort'

  UMAX_INT = 2**32 - 1
  for i in [8, 4, 2]:
    status = compile_and_run(f, s, UMAX_INT/i, args)
    if  status != 'true':
      return status

  return result

def compile_and_run(f, s, n, args):
  s = re.sub("=\s*(__VERIFIER_nondet_uint\(\))", "="+str(n), s)
  s = re.sub("__VERIFIER_assert\((.+)\);", "assert(\\1);", s)
  s = re.sub(r'(extern )?void __VERIFIER_error()', '//', s)
  s = re.sub(r'(extern )?void __VERIFIER_assume()', '//', s)
  s = re.sub(r'__VERIFIER_error\(\)', 'assert(0)', s)
  s = '#include<assert.h>\n' + s

  name = os.path.splitext(os.path.basename(f))[0]
  tmp1 = smack.top.temporary_file(name, '.c', args)
  with open(tmp1, 'w') as fo:
    fo.write(s)

  tmp2 = smack.top.temporary_file(name, '.bin', args)
  tmp2 = tmp2.split('/')[-1]
  #compile and run
  cmd = ['clang', tmp1, '-o', tmp2]

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
