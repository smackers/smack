#! /usr/bin/env python

from os import path
import sys
import re
import subprocess
import argparse
import platform
from smack import *

VERSION = '1.2'


def generateSourceErrorTrace(boogieOutput, bpl):
  FILENAME = '[\w#$~%.\/-]+'
  LABEL = '[\w$]+'

  if not re.search('.*{:sourceloc \"(' + FILENAME + ')\", (\d+), (\d+)}.*', bpl):
#    print 'No debug info in bpl file.'
    return None

  sourceTrace = '\nSMACK verifier version ' + VERSION + '\n\n'
  for traceLine in boogieOutput.splitlines(True):
    resultMatch = re.match('Boogie .* (\d+) verified, (\d+) error.*', traceLine)
    traceMatch = re.match('([ ]+)(' + FILENAME + ')\((\d+),(\d+)\): (' + LABEL + ')', traceLine)
    errorMatch = re.match('(' + FILENAME + ')\((\d+),(\d+)\): (.*)', traceLine)
    if resultMatch:
      verified = int(resultMatch.group(1))
      errors = int(resultMatch.group(2))
      sourceTrace += '\nFinished with ' + str(verified) + ' verified, ' + str(errors) + ' errors\n'
    elif traceMatch:
      spaces = str(traceMatch.group(1))
      filename = str(traceMatch.group(2))
      lineno = int(traceMatch.group(3))
      colno = int(traceMatch.group(4))
      label = str(traceMatch.group(5))

      for bplLine in bpl.splitlines(True)[lineno:lineno+10]:
        m = re.match('.*{:sourceloc \"(' + FILENAME + ')\", (\d+), (\d+)}.*', bplLine)
        if m:
          filename = str(m.group(1))
          lineno = int(m.group(2))
          colno = int(m.group(3))
 
          sourceTrace += spaces + filename + '(' + str(lineno) + ',' + str(colno) + ')\n'
          break
    elif errorMatch:
      filename = str(errorMatch.group(1))
      lineno = int(errorMatch.group(2))
      colno = int(errorMatch.group(3))
      message = str(errorMatch.group(4))
 
      for bplLine in bpl.splitlines(True)[lineno-2:lineno+8]:
        m = re.match('.*{:sourceloc \"(' + FILENAME + ')\", (\d+), (\d+)}.*', bplLine)
        if m:
          filename = str(m.group(1))
          lineno = int(m.group(2))
          colno = int(m.group(3))
 
          sourceTrace += filename + '(' + str(lineno) + ',' + str(colno) + '): ' + message + '\n'
          break
  return sourceTrace
 

if __name__ == '__main__':

  # parse command line arguments
  parser = argparse.ArgumentParser(description='Checks the input LLVM file for assertion violations.', parents=[smackParser()])
  parser.add_argument('--unroll', metavar='N', dest='unroll', default='20', type=int,
                      help='unroll loops/recursion in Boogie/Corral N number of times')
  parser.add_argument('--time-limit', metavar='N', dest='timeLimit', default='1200', type=int,
                      help='Boogie time limit in seconds')
  args = parser.parse_args()

  bpl = smack(path.dirname(sys.argv[0]), args.infile, args.debug, args.memmod, args.verifier, args.entryPoints)

  # write final output
  args.outfile.write(bpl)
  args.outfile.close()

  if args.verifier == 'boogie-plain' or args.verifier == 'boogie-inline':
    # invoke Boogie
    p = subprocess.Popen(['boogie', args.outfile.name, '/nologo', '/timeLimit:' + str(args.timeLimit), '/loopUnroll:' + str(args.unroll)], stdout=subprocess.PIPE)
    boogieOutput = p.communicate()[0]
    sourceTrace = generateSourceErrorTrace(boogieOutput, bpl)
    if sourceTrace:
      print sourceTrace
    else:
      print boogieOutput
  else:
    # invoke Corral
    p = subprocess.Popen(['corral', args.outfile.name, '/recursionBound:' + str(args.unroll)], stdout=subprocess.PIPE)
    corralOutput = p.communicate()[0]
    print corralOutput

