#! /usr/bin/env python

from os import path
import sys
import re
import argparse
import platform
from llvm2bpl import *

VERSION = '1.4.0'


def smackParser():
  parser = argparse.ArgumentParser(add_help=False, parents=[llvm2bplParser()])
  parser.add_argument('--verifier', dest='verifier', choices=['boogie-plain', 'boogie-inline', 'corral'], default='boogie-inline',
                      help='set the underlying verifier format')
  parser.add_argument('--entry-points', metavar='PROC', dest='entryPoints', default='main', nargs='+',
                      help='specify entry procedures')
  parser.add_argument('--unroll', metavar='N', dest='unroll', default='2', type=int,
                      help='unroll loops/recursion in Boogie/Corral N number of times')
  parser.add_argument('--mem-mod', dest='memmod', choices=['no-reuse', 'no-reuse-impls', 'reuse'], default='no-reuse',
                      help='set the memory model (no-reuse=never reallocate the same address, reuse=reallocate freed addresses)')
  return parser


def addInline(match, entryPoints, unroll):
  procName = match.group(1)
  procDef = ''
  if procName in entryPoints:
    procDef += 'procedure ' + procName + '('
  else:
    procDef += 'procedure {:inline ' + str(unroll) + '} ' + procName + '('
  return procDef


def addEntryPoint(match, entryPoints):
  procName = match.group(1)
  procDef = ''
  if procName in entryPoints:
    procDef += 'procedure {:entrypoint} ' + procName + '('
  else:
    procDef += 'procedure ' + procName + '('
  return procDef


def clang(scriptPathName, inputFile, memoryModel):
  scriptFullPath = path.abspath(scriptPathName)
  smackRoot = path.dirname(scriptFullPath)
  smackHeaders = path.join(smackRoot, 'include', 'smack')

  fileName = path.splitext(inputFile.name)[0]

  p = subprocess.Popen(['clang', '-c', '-Wall', '-emit-llvm', '-O0', '-g',
    '-DMEMORY_MODEL_' + memoryModel.upper().replace('-','_'),
    '-I' + smackHeaders, inputFile.name, '-o', fileName + '.bc'])
  p.wait()

  if p.returncode != 0:
    sys.exit("SMACK encountered a clang error. Exiting...")

  inputFileName = path.join(path.curdir, fileName + '.bc')
  inputFile = open(inputFileName, 'r')
  return inputFile


def smackGenerate(sysArgv):

  # parse command line arguments
  parser = argparse.ArgumentParser(description='Outputs the appropriately annotated Boogie file generated from the input LLVM file.', parents=[smackParser()])
  args = parser.parse_args(sysArgv[1:])
  inputFile = args.infile
  scriptPathName = path.dirname(sysArgv[0])

  fileExtension = path.splitext(inputFile.name)[1]
  options = []
  if fileExtension == '.c':
    # if input file is .c, then search for options in comments and compile it with clang
    lines = inputFile.readlines()
    for line in lines:
      optionsMatch = re.match('.*SMACK-OPTIONS:[ ]+(.*)$', line)
      if optionsMatch:
        options = optionsMatch.group(1).split()
        args = parser.parse_args(options + sysArgv[1:])
    inputFile = clang(scriptPathName, inputFile, args.memmod)

  bpl = llvm2bpl(inputFile, args.debug, "impls" in args.memmod)
  inputFile.close()

  p = re.compile('procedure\s+([^\s(]*)\s*\(')
  if args.verifier == 'boogie-inline':
    # put inline on procedures
    bpl = p.sub(lambda match: addInline(match, args.entryPoints, args.unroll), bpl)
  elif args.verifier == 'corral':
    # annotate entry points
    bpl = p.sub(lambda match: addEntryPoint(match, args.entryPoints), bpl)
  return bpl, options


if __name__ == '__main__':

  # parse command line arguments
  parser = argparse.ArgumentParser(description='Outputs the appropriately annotated Boogie file generated from the input LLVM file.', parents=[smackParser()])
  args = parser.parse_args()

  bpl, options = smackGenerate(sys.argv)

  # write final output
  args.outfile.write(bpl)
  args.outfile.close()

