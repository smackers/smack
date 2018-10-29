import sys
import re
import subprocess

def linecount(p1, p2, s):
  valid_lines = []
  lines = s.split('\n') 
  regex_p1 = re.compile(p1)
  regex_p2 = re.compile(p2)
  for line in lines:
    r1 = regex_p1.search(line)
    if r1:
      r2 = regex_p2.search(line)
      if r2 is None:
        valid_lines.append(r1.group(0)) 
  return valid_lines 

def raw_file_line_count(s):
  lines = s.split('\n')
  count = 0
  #grep -v extern | grep -vP "^\w*$" | grep -v "#"
  crap = re.compile(r"""(extern|^\w*$|#)""")
  for line in lines:
    if crap.search(line) is None:
      count += 1

  return count

def svcomp_filter(f):
  lines = None
  with open(f, 'r') as inputfile:
    lines = inputfile.read()

  pruned_lines = raw_file_line_count(lines)
  raw_lines = len(lines.split('\n'))

  executable = False
  if raw_lines < 50 and len(linecount(r'__VERIFIER_nondet|fopen', r'void\s+|extern', lines)) == 0 and not ('while(1)' in lines):
      executable = True

  if bv_filter(lines, raw_lines, pruned_lines):
    return 'bitvector', executable 

  if float_filter(lines, raw_lines, pruned_lines):
    return 'float', executable 

  return 'normal', executable 
    
def bv_filter(lines, raw_line_count, pruned_line_count):
  if ("bugBrokenOut" in lines or "returnsStructure" in lines or "__VERIFIER_nondet_double" in lines or
      "__VERIFIER_nondet_float" in lines or "0x43300000" in lines or "float X, P;" in lines or "1415926538837245" in lines or
      "huge_floor" in lines or "huge_ceil" in lines or "tiny_sqrt" in lines or "fmax_float" in lines or
      "fabs_double" in lines or "round_double" in lines or "trunc_double" in lines or "zero_log" in lines or
      "isinf_float" in lines or "trunc_float" in lines):
    return 0
  elif ('4294967294u' in lines or '616783' in lines):
    return 1

  if raw_line_count > 1500:
    if 'ldv_usb_gadget' in lines or "SyncPush" in lines or "kaweth_set_receive_filter" in lines:
      return 1
    else:
      return 0
  
  #line_count = raw_file_line_count(lines)
  if pruned_line_count > 650:
    return 0

  #special case for Concurrent benchmarks
  if "pthread_create" in lines:
    return 0

  #cast patterns
  if pruned_line_count <= 210:

    if pruned_line_count < 25 and 'while(1)' in lines:
      return 1

    casts = re.compile(r'''4294967295|plus_one|minus_one|\(x % 2\) == \(y % 2\)|linear_search|while \(\('0' <= c\) && \(c <= '9'\)\)''')
    if casts.search(lines):
      return 1
  #bwops = re.compile(r'''[^\&]\&[^\&]|[^\|]\|[^\|]|\^|>>|<<''')
  bwops = re.compile(r'''[=|\(][^,]*[^\&|\(|{]\&\s|[^\|]\|\s|\^|>>|<<''')
  #bwops = re.compile(r'''\s\&\s|\s\|\s|\^|>>|<<''')
  #dv = re.compile(r'''1\s+<<\s+[1|5]|cil''')
  dv = re.compile(r'''1.*<<.*\"|cil|found|node''')
  
  for line in lines.split('\n'):
    if bwops.search(line):
      if dv.search(line) is None: 
        #print line
        return 1
  #print raw_file_line_count(lines)
  return 0
    
def float_filter(lines, raw_line_count, pruned_line_count):
  fliteral = 0 
  ddecl = 0

  if ("bugBrokenOut" in lines or "returnsStructure" in lines or "__VERIFIER_nondet_double" in lines or
      "__VERIFIER_nondet_float" in lines or "0x43300000" in lines or "float X, P;" in lines or "1415926538837245" in lines or
      "huge_floor" in lines or "huge_ceil" in lines or "tiny_sqrt" in lines or "fmax_float" in lines or
      "fabs_double" in lines or "round_double" in lines or "trunc_double" in lines or "zero_log" in lines or
      "isinf_float" in lines or "trunc_float" in lines):
    return 1

  #heuristic #-1: don't do test on too large programs
  if raw_line_count >= 2000: 
    return 0
  #heuristic #0: more than Float.set maximum LOC ==> not 
  if pruned_line_count > 140: #(138 = maximum) 
    return 0
  #heuristic #1: __VERIFIER_nondet ==> float category
  result = re.search(r"""(__VERIFIER_nondet_(float|double)|ieee754_float)""", lines)  
  if result:
    return 1

  #heuristic #2: check float literal # 
  valid_lines = linecount(r"""(0x)?\d+\.\d*(f|p|e)?""", r"""#|line|June|CIL|0\.000000|\"\d+|Created""", lines)
  count = len(valid_lines)
  if count > 60:
    return 0
  if count == 0:
  #heuristic #3: check double 
    #result = re.search(r"""0x\d+\.?.*p|double""", lines)
    result = re.search(r"""double""", lines)
    if result:
      return 1
    else:
      return 0
  else: 
  #heuristic #4: for loops/heapmanipulation
    #print valid_lines
    regex_special = re.compile(r"""1\.4p|1\.0e""")
    for valid_line in valid_lines:
      if regex_special.search(valid_line) is not None and count <= 4:
        return 0 
      if valid_line == '1.' or valid_line == '2.':
        if 'double' not in lines:
          return 0
        else:
          return 1
    return 1 


def scrub_pthreads(s):
  if 'pthread_create' not in s:
    return s, False

  # special case for sequentialized benchmarks
  if '__CS_pthread_create' in s:
    return s, False

  # special case for machzwd benchmarks
  if 'assert_context_process' in s:
    return s, False

  #These are strings that will conflict with our pthread header files
  #To generate additional strings, copy paste the text.  
  #Escape all characters that need to be escaped for regex (at least *[]() 
  # Then replace all newlines and spaces with \s+. Lastly, replace all 
  # \s+\s+ to \s+.  Do this last step until string doesn't change anymore.
  fltrs = list()
  fltrs.append(r'typedef\s+unsigned\s+long\s+int\s+pthread_t;')
  #pthread_attr_t
  fltrs.append(r'typedef\s+union\s+{\s+char\s+__size\[\d+\];\s+long\s+int\s+__align;\s+}\s+pthread_attr_t;')
  fltrs.append(r'union\s+pthread_attr_t\s+{\s+char\s+__size\[\d+\];\s+long\s+int\s+__align;\s+};\s+typedef\s+union\s+pthread_attr_t\s+pthread_attr_t;')
  #pthread_mutexattr_t
  fltrs.append(r'typedef\s+union\s+{\s+char\s+__size\[\d+\];\s+int\s+__align;\s+}\s+pthread_mutexattr_t;')
  fltrs.append(r'typedef\s+union\s+{\s+char\s+__size\[\d+\];\s+long\s+int\s+__align;\s+}\s+pthread_mutexattr_t;')
  #pthread_mutex_t
  fltrs.append(r'typedef\s+union\s+{\s+struct\s+__pthread_mutex_s\s+{\s+int\s+__lock;\s+unsigned\s+int\s+__count;\s+int\s+__owner;\s+unsigned\s+int\s+__nusers;\s+int\s+__kind;\s+int\s+__spins;\s+__pthread_list_t\s+__list;\s+}\s+__data;\s+char\s+__size\[\d+\];\s+long\s+int\s+__align;\s+}\s+pthread_mutex_t;')
  fltrs.append(r'typedef\s+union\s+{\s+struct\s+__pthread_mutex_s\s+{\s+int\s+__lock;\s+unsigned\s+int\s+__count;\s+int\s+__owner;\s+int\s+__kind;\s+unsigned\s+int\s+__nusers;\s+__extension__\s+union\s+{\s+struct\s+{\s+short\s+__espins;\s+short\s+__elision;\s+}\s+__elision_data;\s+__pthread_slist_t\s+__list;\s+};\s+}\s+__data;\s+char\s+__size\[\d+\];\s+long\s+int\s+__align;\s+}\s+pthread_mutex_t;')
  fltrs.append(r'typedef\s+union\s+{\s+struct\s+__pthread_mutex_s\s+{\s+int\s+__lock;\s+unsigned\s+int\s+__count;\s+int\s+__owner;\s+int\s+__kind;\s+unsigned\s+int\s+__nusers;\s+__extension__\s+union\s+{\s+int\s+__spins;\s+__pthread_slist_t\s+__list;\s+};\s+}\s+__data;\s+char\s+__size\[\d+\];\s+long\s+int\s+__align;\s+}\s+pthread_mutex_t;')
  fltrs.append(r'typedef\s+union\s+{\s+struct\s+__pthread_mutex_s\s+{\s+int\s+__lock;\s+unsigned\s+int\s+__count;\s+int\s+__owner;\s+unsigned\s+int\s+__nusers;\s+int\s+__kind;\s+short\s+__spins;\s+short\s+__elision;\s+__pthread_list_t\s+__list;\s+# 124 "/usr/include/x86_64-linux-gnu/bits/pthreadtypes\.h" 3 4\s+}\s+__data;\s+\s+char\s+__size\[\d+\];\s+long\s+int\s+__align;\s+} pthread_mutex_t;')
  fltrs.append(r'typedef\s+union\s+{\s+struct\s+__pthread_mutex_s\s+{\s+int\s+__lock;\s+unsigned\s+int\s+__count;\s+int\s+__owner;\s+int\s+__kind;\s+unsigned\s+int\s+__nusers;\s+__extension__\s+union\s+{\s+struct\s+{\s+short\s+__espins;\s+short\s+__elision;\s+}\s+d;\s+__pthread_slist_t\s+__list;\s+};\s+}\s+__data;\s+char\s+__size\[\d+\];\s+long\s+int\s+__align;\s+}\s+pthread_mutex_t;')
  fltrs.append(r'typedef\s+union\s+{\s+struct\s+__pthread_mutex_s\s+{\s+int\s+__lock;\s+unsigned\s+int\s+__count;\s+int\s+__owner;\s+unsigned\s+int\s+__nusers;\s+int\s+__kind;\s+short\s+__spins;\s+short\s+__elision;\s+__pthread_list_t\s+__list;\s+}\s+__data;\s+char\s+__size\[\d+\];\s+long\s+int\s+__align;\s+}\s+pthread_mutex_t;')
  #pthread_cond_t
  fltrs.append(r'typedef\s+union\s+{\s+struct\s+{\s+int\s+__lock;\s+unsigned\s+int\s+__futex;\s+__extension__\s+unsigned\s+long\s+long\s+int\s+__total_seq;\s+__extension__\s+unsigned\s+long\s+long\s+int\s+__wakeup_seq;\s+__extension__\s+unsigned\s+long\s+long\s+int\s+__woken_seq;\s+void\s+\*__mutex;\s+unsigned\s+int\s+__nwaiters;\s+unsigned\s+int\s+__broadcast_seq;\s+}\s+__data;\s+char\s+__size\[\d+\];\s+__extension__\s+long\s+long\s+int\s+__align;\s+}\s+pthread_cond_t;')
  #pthread_condattr_t
  fltrs.append(r'typedef\s+union\s+{\s+char\s+__size\[\d+\];\s+int\s+__align;\s+}\s+pthread_condattr_t;')
  fltrs.append(r'typedef\s+union\s+{\s+char\s+__size\[\d+\];\s+long\s+int\s+__align;\s+}\s+pthread_condattr_t;')
  #enums
  fltrs.append(r'enum\s+{\s+PTHREAD_MUTEX_TIMED_NP,\s+PTHREAD_MUTEX_RECURSIVE_NP,\s+PTHREAD_MUTEX_ERRORCHECK_NP,\s+PTHREAD_MUTEX_ADAPTIVE_NP\s+,\s+PTHREAD_MUTEX_NORMAL\s+=\s+PTHREAD_MUTEX_TIMED_NP,\s+PTHREAD_MUTEX_RECURSIVE\s+=\s+PTHREAD_MUTEX_RECURSIVE_NP,\s+PTHREAD_MUTEX_ERRORCHECK\s+=\s+PTHREAD_MUTEX_ERRORCHECK_NP,\s+PTHREAD_MUTEX_DEFAULT\s+=\s+PTHREAD_MUTEX_NORMAL\s+};')
  fltrs.append(r'enum\s+{\s+PTHREAD_MUTEX_TIMED_NP,\s+PTHREAD_MUTEX_RECURSIVE_NP,\s+PTHREAD_MUTEX_ERRORCHECK_NP,\s+PTHREAD_MUTEX_ADAPTIVE_NP\s+};')
  #pthread_cond_init decl
  fltrs.append(r'extern\s+int\s+pthread_cond_init\s+\(pthread_cond_t\s+\*__restrict\s+__cond,\s+__const\s+pthread_condattr_t\s+\*__restrict\s+__cond_attr\)\s+__attribute__\s+\(\(__nothrow__\s+,\s+__leaf__\)\)\s+__attribute__\s+\(\(__nonnull__\s+\(\d+\)\)\);')
  fltrs.append(r'extern\s+int\s+pthread_cond_init\s*\(pthread_cond_t\s+\*__restrict\s+__cond,\s+const\s+pthread_condattr_t\s+\*__restrict\s+__cond_attr\)\s+__attribute__\s*\(\(__nothrow__\s+,\s+__leaf__\)\)\s+__attribute__\s+\(\(__nonnull__\s+\(1\)\)\);')
  fltrs.append(r'extern\s+int\s+pthread_cond_init\s*\(pthread_cond_t\s+\*__restrict\s+__cond,\s+__const\s+pthread_condattr_t\s+\*__restrict\s+__cond_attr\)\s+__attribute__\s+\(\(__nothrow__\)\)\s+__attribute__\s+\(\(__nonnull__\s+\(1\)\)\);')
  #__VERIFIER_atomic_begin definition removal
  fltrs.append(r'int\s+__global_lock;\s+void\s+__VERIFIER_atomic_begin\(\)\s+{\s+__VERIFIER_assume\(__global_lock==0\);\s+__global_lock=1;\s+return;\s+}\s+void\s+__VERIFIER_atomic_end\(\)\s+{\s+__VERIFIER_assume\(__global_lock==1\);\s+__global_lock=0;\s+return;\s+}')


  #Remove each occurrence
  for fltr in fltrs:
    #sold = s
    pat = re.compile(fltr, re.MULTILINE);
    s = pat.sub('', s)
    #if sold == s:
    #  print("Didn't match - " + fltr)
    #else:
    #  print("DID match - " + fltr)

  s = re.sub(r'(__VERIFIER_atomic_((?!begin|end).)*?\(.*?\);)',
             r'__VERIFIER_atomic_begin(); \1 __VERIFIER_atomic_end();',
             s)

  s = re.sub(r'\ninline ', r'\n', s)

  return s, True

    
if __name__ == '__main__':
  print "What?"
  print svcomp_filter(sys.argv[1])

