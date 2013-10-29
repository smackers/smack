#! /usr/bin/env python

from os import path
import sys
import subprocess
import argparse
import io
import platform

VERSION = '1.3.1'


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
                      type=argparse.FileType('w'),
                      help='output Boogie file (default: %(default)s)')
  parser.add_argument('-d', '--debug', dest='debug', action="store_true", default=False,
                      help='turn on debug info')
  parser.add_argument('--mem-mod', dest='memmod', choices=['flat', 'twodim'], default='flat',
                      help='set the memory model (flat=flat memory model, twodim=two dimensional memory model)')
  return parser


def find_install_prefix(smackRoot):
  installPrefix = path.join(smackRoot, 'Debug+Asserts')
  if not path.exists(installPrefix):
    installPrefix = path.join(smackRoot, 'Release+Asserts')
  if not path.exists(installPrefix):
    installPrefix = smackRoot
  assert path.exists(installPrefix)
  return installPrefix


def find_library_path(installPrefix):
  libraryPath = path.join(installPrefix, 'lib', 'smack.so')
  if not path.exists(libraryPath):
    libraryPath = path.join(installPrefix, 'lib', 'smack.dylib')
  if not path.exists(libraryPath):
    libraryPath = path.join(installPrefix, 'bin', 'smack.dll')
  assert path.exists(libraryPath)
  return libraryPath


def llvm2bpl(scriptPathName, infile, debugFlag, memmod):

  # find library paths
  scriptFullPath = path.abspath(scriptPathName)
  smackRoot = path.dirname(scriptFullPath)
  installPrefix = find_install_prefix(smackRoot)
  libraryPath = find_library_path(installPrefix)

  # invoke SMACK LLVM module
  if debugFlag:
    p = subprocess.Popen(['opt', '-load=' + libraryPath, '-internalize', '-mem2reg',
      '-source-loc-syms',
      '-die', '-lowerswitch', '-bpl_print', '-mem-mod=' + memmod, '-debug', '-o=tmp.bc'],
      stdin=infile, stderr=subprocess.PIPE)
  else:
    p = subprocess.Popen(['opt', '-load=' + libraryPath, '-internalize', '-mem2reg',
      '-source-loc-syms',
      '-die', '-lowerswitch', '-bpl_print', '-mem-mod=' + memmod, '-debug-only=bpl', '-o=tmp.bc'],
      stdin=infile, stderr=subprocess.PIPE)
  output = p.communicate()[1]
  bplStartIndex = output.find('// SMACK-PRELUDE-BEGIN')
  debug = output[0:bplStartIndex]
  if p.returncode != 0:
    if debugFlag:
      print debug
    print >> sys.stderr, "LLVM/SMACK encountered an error:"
    print >> sys.stderr, output[0:1000], "... (output truncated)"
    sys.exit("LLVM/SMACK returned exit status %s" % p.returncode)
  bpl = output[bplStartIndex:]
  return debug, bpl
 

if __name__ == '__main__':

  # parse command line arguments
  parser = argparse.ArgumentParser(description='Outputs a plain Boogie file generated from the input LLVM file.', parents=[llvm2bplParser()])
  args = parser.parse_args()

  debug, bpl = llvm2bpl(path.dirname(sys.argv[0]), args.infile, args.debug, args.memmod)

  # print debug info
  if args.debug:
    print debug

  # write final output
  args.outfile.write(bpl)
  args.outfile.close()

