#! /usr/bin/env python

from os import path
import sys
import re
import subprocess
import argparse
import platform
from llvm2bpl import *

VERSION = '1.2'


def addInline(match, entryPoints):
  procName = match.group(1)
  procDef = ''
  if procName in entryPoints:
    procDef += 'procedure ' + procName + '('
  else:
    procDef += 'procedure {:inline 1} ' + procName + '('
  return procDef


def addEntryPoint(match, entryPoints):
  procName = match.group(1)
  procDef = ''
  if procName in entryPoints:
    procDef += 'procedure {:entrypoint} ' + procName + '('
  else:
    procDef += 'procedure ' + procName + '('
  return procDef


def generateSourceErrorTrace(boogieOutput, bpl):
  FILENAME = '[\w#$~%.\/-]+'
  LABEL = '[\w$]+'

  if not re.search('.*{:sourceloc \"(' + FILENAME + ')\", (\d+), (\d+)}.*', bpl):
#    print 'No debug info in bpl file.'
    return None

  sourceTrace = '\nSMACK checker version ' + VERSION + '\n\n'
  for traceLine in boogieOutput.splitlines(True):
    resultMatch = re.match('Boogie .* (\d+) verified, (\d+) error.*', traceLine)
    traceMatch = re.match('([ ]+)(' + FILENAME + ')\((\d+),(\d+)\): (' + LABEL + ')', traceLine)
    errorMatch = re.match('(' + FILENAME + ')\((\d+),(\d+)\): (.*)', traceLine)
    if resultMatch:
      verified = int(resultMatch.group(1))
      errors = int(resultMatch.group(2))
      sourceTrace += '\nFinished with ' + str(verified) + ' checked, ' + str(errors) + ' errors\n'
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
  parser = argparse.ArgumentParser(description='Checks the input LLVM file for assertion violations.', parents=[llvm2bplParser()])
  parser.add_argument('--checker', dest='checker', choices=['boogie', 'corral'], default='boogie',
                      help='set the underlying checker')
  parser.add_argument('--entry-points', metavar='PROC', dest='entryPoints', default='main', nargs='+',
                      help='specify entry procedures')
  parser.add_argument('--loop-unroll', metavar='N', dest='loopUnroll', default='20', type=int,
                      help='unroll loops in Boogie N number of times')
  parser.add_argument('--time-limit', metavar='N', dest='timeLimit', default='1200', type=int,
                      help='Boogie time limit in seconds')
  args = parser.parse_args()

  debug, bpl = llvm2bpl(path.dirname(sys.argv[0]), args.infile, args.debug, args.memmod)

  # print debug info
  if args.debug:
    print debug

  p = re.compile('procedure[ ]*([a-zA-Z0-9_]*)[ ]*\(')
  if args.checker == 'boogie':
    # put inline on procedures
    bpl = p.sub(lambda match: addInline(match, args.entryPoints), bpl)
  else:
    # annotate entry points
    bpl = p.sub(lambda match: addEntryPoint(match, args.entryPoints), bpl)

  # write final output
  args.outfile.write(bpl)
  args.outfile.close()

  if args.checker == 'boogie':
    # invoke Boogie
    p = subprocess.Popen(['boogie', args.outfile.name, '/nologo', '/timeLimit:' + str(args.timeLimit), '/loopUnroll:' + str(args.loopUnroll)], stdout=subprocess.PIPE)
    boogieOutput = p.communicate()[0]
    sourceTrace = generateSourceErrorTrace(boogieOutput, bpl)
    if sourceTrace:
      print sourceTrace
    else:
      print boogieOutput
  else:
    # invoke Corral
    p = subprocess.Popen(['corral', args.outfile.name], stdout=subprocess.PIPE)
    corralOutput = p.communicate()[0]
    print corralOutput

