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
  
    
def float_filter(b):
  lines = None
  with open(b, 'r') as inputfile:
    lines = inputfile.read()
  fliteral = 0 
  ddecl = 0

  #heuristic #-1: don't do test on too large programs
  if len(lines.split('\n')) >= 2000: 
    return 0
  #heuristic #0: more than Float.set maximum LOC ==> not 
  if raw_file_line_count(lines) > 140: #(138 = maximum) 
    return 0
  #heuristic #1: __VERIFIER_nondet ==> float category
  result = re.search(r"""(__VERIFIER_nondet_(float|double)|ieee754_float)""", lines)  
  if result:
    return 1

  #heuristic #2: check float literal # 
  valid_lines = linecount(r"""(0x)?\d+\.\d*(f|p|e)?""", r"""#|line|June|CIL|0\.000000|\"\d+""", lines)
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
    
if __name__ == '__main__':
    
  print float_filter(sys.argv[1])
