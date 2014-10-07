#!/usr/bin/env python
#
# This file is distributed under the MIT License. See LICENSE for details.
#

from os import path
import sys
import subprocess
import argparse
import io
import platform

VERSION = '1.4.1'


def is_valid_file(parser, arg):
  if not path.isfile(arg):
    parser.error("the file %s does not exist!"%arg)
  else:
    return open(arg, 'r')


def llvm2bplParser():
  parser = argparse.ArgumentParser(add_help=False)
  parser.add_argument('-v', '--version', action='version', version='SMACK version ' + VERSION)
  parser.add_argument('infile', metavar='<file>',
                      type=lambda x: is_valid_file(parser,x),
                      help='input LLVM file')
  parser.add_argument('-o', '--output', dest='outfile', metavar='<file>', default='a.bpl',
                      type=str,
                      help='output Boogie file (default: %(default)s)')
  parser.add_argument('-d', '--debug', dest='debug', action="store_true", default=False,
                      help='turn on debug info')
  parser.add_argument('--mem-mod', dest='memmod', choices=['no-reuse', 'no-reuse-impls', 'reuse'], default='no-reuse',
                      help='set the memory model (no-reuse=never reallocate the same address, reuse=reallocate freed addresses)')
  return parser


def llvm2bpl(infile, outfile, debugFlag, memImpls):
    
  cmd = ['smack', '-source-loc-syms', infile.name]
  if debugFlag: cmd.append('-debug')
  if memImpls: cmd.append('-mem-mod-impls')
  cmd.append('-o=' + outfile)
  p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
  smackOutput = p.communicate()[0]

  if p.returncode:
    print >> sys.stderr, smackOutput
    sys.exit("SMACK encountered an error when invoking SMACK tool. Exiting...")

  with open(outfile, 'r') as outputFile:
    output = outputFile.read()
    outputFile.close()

  # bplStartIndex = output.find('// SMACK-PRELUDE-BEGIN')
  # bpl = output[bplStartIndex:]
  # return bpl
  return output
 

if __name__ == '__main__':

  # parse command line arguments
  parser = argparse.ArgumentParser(description='Outputs a plain Boogie file generated from the input LLVM file.', parents=[llvm2bplParser()])
  args = parser.parse_args()

  bpl = llvm2bpl(args.infile, args.outfile, args.debug, "impls" in args.memmod)

  # write final output
  with open(args.outfile, 'w') as outputFile:
    outputFile.write(bpl)
    outputFile.close()

