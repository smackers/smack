#!/usr/bin/env python
#
# This file is distributed under the MIT License. See LICENSE for details.
#

from os import path
import sys
import re
import argparse
import platform
from llvm2bpl import *

VERSION = '1.4.1'


def smackParser():
  parser = argparse.ArgumentParser(add_help=False, parents=[llvm2bplParser()])
  parser.add_argument('--clang', dest='clang', default='',
                      help='pass arguments to clang (e.g., --clang="-w -g")')
  parser.add_argument('--verifier', dest='verifier', choices=['boogie', 'corral', 'duality'], default='boogie',
                      help='set the underlying verifier format')
  parser.add_argument('--entry-points', metavar='PROC', dest='entryPoints', default='main', nargs='+',
                      help='specify entry procedures')
  parser.add_argument('--unroll', metavar='N', dest='unroll', type=int,
                      help='unroll loops/recursion in Boogie/Corral N number of times')
  parser.add_argument('--bc', dest='bcfile', metavar='<file>', type=str,
                      help='output clang (bc) file')
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


def clang(scriptPathName, inputFile, bcFileName, outputFileName, memoryModel, clangArgs):
  scriptFullPath = path.abspath(scriptPathName)
  smackRoot = path.dirname(scriptFullPath)
  smackHeaders = path.join(smackRoot, 'include', 'smack')

  fileName, fileExtension = path.splitext(path.basename(inputFile.name))

  if bcFileName is None:
    bcFileName = path.join(path.dirname(path.abspath(outputFileName)),
      fileName) + '.bc'

  if fileExtension in ['.c']:
    clangCommand = ['clang']
  elif fileExtension in ['.cc', '.cpp']:
    clangCommand = ['clang++']
  else:
    sys.exit('Unexpected source file extension `' + fileExtension + '\'')

  clangCommand += ['-c', '-emit-llvm', '-O0', '-g', '-gcolumn-info',
                   '-DMEMORY_MODEL_' + memoryModel.upper().replace('-','_'),
                   '-I' + smackHeaders,
                   '-include' + 'smack.h']
  clangCommand += clangArgs.split()
  clangCommand += [inputFile.name, '-o', bcFileName]
  #Redirect stderr to stdout, then grab stdout (communicate() calls wait())
  #This should more or less maintain stdout/stderr interleaving order
  #However, this will be problematic if any callers want to differentiate
  #    between clangs stdout and stderr.
  p = subprocess.Popen(clangCommand, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
  clangOutput = p.communicate()[0]

  if p.returncode:
    print >> sys.stderr, clangOutput
    sys.exit("SMACK encountered an error when invoking clang. Exiting...")

  inputFile = open(bcFileName, 'r')
  return inputFile, clangOutput


def smackGenerate(sysArgv):

  # parse command line arguments
  parser = argparse.ArgumentParser(description='Outputs the appropriately annotated Boogie file generated from the input LLVM file.', parents=[smackParser()])
  args = parser.parse_args(sysArgv[1:])
  inputFile = args.infile
  scriptPathName = path.dirname(sysArgv[0])
  clangOutput = None

  fileExtension = path.splitext(inputFile.name)[1]
  options = []
  if fileExtension in ['.c','.cc','.cpp']:
    # if input file is .c, then search for options in comments and compile it with clang
    lines = inputFile.readlines()
    for line in lines:
      optionsMatch = re.match('.*SMACK-OPTIONS:[ ]+(.*)$', line)
      if optionsMatch:
        options = optionsMatch.group(1).split()
        args = parser.parse_args(options + sysArgv[1:])
    inputFile, clangOutput = clang(scriptPathName, inputFile, args.bcfile, args.outfile, args.memmod, args.clang)

  elif fileExtension in ['.bc', '.ll']:
    pass # do nothing
  else:
    sys.exit('Unexpected source file extension `' + fileExtension + '\'')

  bpl = llvm2bpl(inputFile, args.outfile, args.debug, "impls" in args.memmod)
  inputFile.close()

  p = re.compile('procedure\s+([^\s(]*)\s*\(')
  si = re.compile('procedure\s+(\$static_init|__SMACK_.*|assert_|assume_|__VERIFIER_.*)\s*\(')

  if args.verifier == 'boogie' and args.unroll is None:
    bpl = si.sub(lambda match: addInline(match, args.entryPoints, 1), bpl)

  elif args.verifier == 'boogie':
    # put inline on procedures
    bpl = p.sub(lambda match: addInline(match, args.entryPoints, args.unroll), bpl)
  elif args.verifier == 'corral' or args.verifier == 'duality':
    # annotate entry points
    bpl = p.sub(lambda match: addEntryPoint(match, args.entryPoints), bpl)

  return bpl, options, clangOutput


if __name__ == '__main__':

  # parse command line arguments
  parser = argparse.ArgumentParser(description='Outputs the appropriately annotated Boogie file generated from the input LLVM file.', parents=[smackParser()])
  args = parser.parse_args()

  bpl, options, clangOutput = smackGenerate(sys.argv)
  if clangOutput is not None:
    print clangOutput

  # write final output
  with open(args.outfile, 'w') as outputFile:
    outputFile.write(bpl)
    outputFile.close()

