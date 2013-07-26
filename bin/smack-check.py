#! /usr/bin/env python

from os import path
import sys
import re
import subprocess
import argparse
import platform
from llvm2bpl import *

VERSION = '1.2'


def addInline(match):
  procName = match.group(1)
  procDef = ''
  if procName == 'main':
    procDef += 'procedure ' + procName + '('
  else:
    procDef += 'procedure {:inline 1} ' + procName + '('
  return procDef


def addEntryPoint(match):
  procName = match.group(1)
  procDef = ''
  if procName == 'main':
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
  parser = argparse.ArgumentParser(description='Outputs a Boogie file generated from the input LLVM file.')
  parser.add_argument('-v', '--version', action='version', version='SMACK version ' + VERSION)
  parser.add_argument('infile', metavar='<file>',
                      type=lambda x: is_valid_file(parser,x),
                      help='input LLVM file')
  parser.add_argument('-o', '--output', dest='outfile', metavar='<file>', default='a.bpl',
                      type=argparse.FileType('w'),
                      help='output Boogie file (default: %(default)s)')
  parser.add_argument('-d', '--debug', dest='debug', action="store_true", default=False,
                      help='turn on debug info')
  parser.add_argument('--mem-mod', dest='memmod', choices=['flat', 'twodim'], default='flat',
                      help='set the memory model (flat=flat memory model, twodim=two dimensional memory model)')
  parser.add_argument('--checker', dest='checker', choices=['boogie', 'corral'], default='boogie',
                      help='set the underlying checker')
  parser.add_argument('--loop-unroll', metavar='N', dest='loopUnroll', default='20', type=int,
                      help='unroll loops in Boogie N number of times')
  parser.add_argument('--time-limit', metavar='N', dest='timeLimit', default='1200', type=int,
                      help='Boogie time limit in seconds')
  args = parser.parse_args()

  debug, bpl = llvm2bpl(path.dirname(sys.argv[0]), args.infile, args.debug, args.memmod)

  # print debug info
  if args.debug:
    print debug

  # put inline on procedures
  p = re.compile('procedure[ ]*([a-zA-Z0-9_]*)[ ]*\(')
  if args.checker == 'boogie':
    bpl = p.sub(lambda match: addInline(match), bpl)
  else:
    bpl = p.sub(lambda match: addEntryPoint(match), bpl)

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

