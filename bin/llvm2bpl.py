#! /usr/bin/env python

from os import path
import sys
import subprocess
import argparse
import io
import platform


def is_valid_file(parser, arg):
  if not path.isfile(arg):
    parser.error("the file %s does not exist!"%arg)
  else:
    return open(arg, 'r')

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

def llvm2bpl(scriptPathName, infile):

  # find prelude and library paths
  scriptFullPath = path.abspath(scriptPathName)
  smackRoot = path.dirname(scriptFullPath)
  installPrefix = find_install_prefix(smackRoot)
  libraryPath = find_library_path(installPrefix)
  preludePath = path.join(installPrefix, 'include', 'prelude-int.bpl')

  # load prelude
  preludeFile = open(preludePath)
  prelude = preludeFile.read()
  preludeFile.close()

  # invoke SMACK LLVM module
  p = subprocess.Popen(['opt', '-load=' + libraryPath, '-internalize', '-mem2reg',
    '-die', '-lowerswitch', '-bpl_print', '-debug-only=bpl', '-o=tmp.bc'],
    stdin=infile, stderr=subprocess.PIPE)
  bplOutput = p.communicate()[1]
  bplOutput = prelude + bplOutput
  return bplOutput
 

if __name__ == '__main__':

  # parse command line arguments
  parser = argparse.ArgumentParser(description='Outputs a Boogie file generated from the input LLVM file.')
  parser.add_argument('infile', metavar='<file>',
                      type=lambda x: is_valid_file(parser,x),
                      help='input LLVM file')
  parser.add_argument('-o', '--output', dest='outfile', metavar='<file>', default='a.bpl',
                      type=argparse.FileType('w'),
                      help='output Boogie file (default: %(default)s)')
  args = parser.parse_args()

  bplOutput = llvm2bpl(path.dirname(sys.argv[0]), args.infile)

  # write final output
  args.outfile.write(bplOutput)
  args.outfile.close()

