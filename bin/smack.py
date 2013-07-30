#! /usr/bin/env python

from os import path
import sys
import re
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


if __name__ == '__main__':

  # parse command line arguments
  parser = argparse.ArgumentParser(description='Outputs the appropriately annotated Boogie file generated from the input LLVM file.', parents=[llvm2bplParser()])
  parser.add_argument('--format', dest='format', choices=['boogie-plain', 'boogie-inline', 'corral'], default='boogie-plain',
                      help='choose the appropriate output format')
  parser.add_argument('--entry-points', metavar='PROC', dest='entryPoints', default='main', nargs='+',
                      help='specify entry procedures')
  args = parser.parse_args()

  scriptPathName = path.dirname(sys.argv[0])
  scriptFullPath = path.abspath(scriptPathName)
  smackRoot = path.dirname(scriptFullPath)
  smackHeaders = path.join(smackRoot, 'include')

  inputFile = args.infile
  fileName, fileExtension = path.splitext(inputFile.name)

  if fileExtension == '.c':
    # if input file is .c, then compile it first with clang
    p = subprocess.Popen(['clang', '-c', '-Wall', '-emit-llvm', '-O0', '-g',
      '-I' + smackHeaders, inputFile.name, '-o', fileName + '.bc'])
    p.wait()
    inputFileName = path.join(path.curdir, fileName + '.bc')
    inputFile = open(inputFileName, 'r')

  debug, bpl = llvm2bpl(scriptPathName, inputFile, args.debug, args.memmod)
  inputFile.close()

  # print debug info
  if args.debug:
    print debug

  p = re.compile('procedure[ ]*([a-zA-Z0-9_]*)[ ]*\(')
  if args.format == 'boogie-inline':
    # put inline on procedures
    bpl = p.sub(lambda match: addInline(match, args.entryPoints), bpl)
  elif args.format == 'corral':
    # annotate entry points
    bpl = p.sub(lambda match: addEntryPoint(match, args.entryPoints), bpl)

  # write final output
  args.outfile.write(bpl)
  args.outfile.close()

