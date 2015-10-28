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

  if bv_filter(lines, raw_lines, pruned_lines):
    return 'bitvector' 

  if float_filter(lines, raw_lines, pruned_lines):
    return 'float' 

  return 'normal' 
    
def bv_filter(lines, raw_line_count, pruned_line_count):

  if raw_line_count > 1500:
    return 0
  
  #line_count = raw_file_line_count(lines)
  if pruned_line_count > 650:
    return 0
  
  #cast patterns
  if pruned_line_count <= 210:
    casts = re.compile(r'''4294967295|plus_one|minus_one|\(x % 2\) == \(y % 2\)|linear_search''')
    if casts.search(lines):
      return 1
  #bwops = re.compile(r'''[^\&]\&[^\&]|[^\|]\|[^\|]|\^|>>|<<''')
  bwops = re.compile(r'''[=|\(][^,]*[^\&|\(|{]\&\s|[^\|]\|\s|\^|>>|<<''')
  #bwops = re.compile(r'''\s\&\s|\s\|\s|\^|>>|<<''')
  #dv = re.compile(r'''1\s+<<\s+[1|5]|cil''')
  dv = re.compile(r'''1.*<<.*\"|cil|found''')
  
  for line in lines.split('\n'):
    if bwops.search(line):
      if dv.search(line) is None: 
        print line
        return 1
  #print raw_file_line_count(lines)
  return 0
    
def float_filter(lines, raw_line_count, pruned_line_count):
  fliteral = 0 
  ddecl = 0

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
    return 1 


def scrub_pthreads(s):
  if 'pthread' not in s:
    return s, False
  #These are strings that will conflict with our pthread header files
  fltrs = list()
  fltrs[0] = r'typedef unsigned long int pthread_t;'
  fltrs[1] = r'typedef union\n{\n  char __size[56];\n  long int __align;\n} pthread_attr_t;'
  fltrs[2] = r'typedef union\n{\n  char __size[4];\n  int __align;\n} pthread_mutexattr_t;'
  fltrs[3] = r'typedef union\n{\n  struct __pthread_mutex_s\n  {\n    int __lock;\n    unsigned int __count;\n    int __owner;\n    unsigned int __nusers;\n    int __kind;\n    int __spins;\n    __pthread_list_t __list;\n  } __data;\n  char __size[40];\n  long int __align;\n} pthread_mutex_t;'
  fltrs[4] = r'typedef union\n{\n  struct\n  {\n    int __lock;\n    unsigned int __futex;\n    __extension__ unsigned long long int __total_seq;\n    __extension__ unsigned long long int __wakeup_seq;\n    __extension__ unsigned long long int __woken_seq;\n    void *__mutex;\n    unsigned int __nwaiters;\n    unsigned int __broadcast_seq;\n  } __data;\n  char __size[48];\n  __extension__ long long int __align;\n} pthread_cond_t;'
  fltrs[5] = r'typedef union\n{\n  char __size[4];\n  int __align;\n} pthread_condattr_t;'
  fltrs[6] = r'enum\n{\n  PTHREAD_MUTEX_TIMED_NP,\n  PTHREAD_MUTEX_RECURSIVE_NP,\n  PTHREAD_MUTEX_ERRORCHECK_NP,\n  PTHREAD_MUTEX_ADAPTIVE_NP\n  ,\n  PTHREAD_MUTEX_NORMAL = PTHREAD_MUTEX_TIMED_NP,\n  PTHREAD_MUTEX_RECURSIVE = PTHREAD_MUTEX_RECURSIVE_NP,\n  PTHREAD_MUTEX_ERRORCHECK = PTHREAD_MUTEX_ERRORCHECK_NP,\n  PTHREAD_MUTEX_DEFAULT = PTHREAD_MUTEX_NORMAL\n};'

  #Remove each occurrence, but keep newlines so line numbers match
  for fltr in f:
    s = re.sub(fltr, '\n'*fltr.count('\n'), s)

  return s, True

    
if __name__ == '__main__':
    
  print float_filter(sys.argv[1])
