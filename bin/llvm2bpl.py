#! /usr/bin/env python

from os import path
import sys
import subprocess
import argparse
import io


def is_valid_file(parser, arg):
  if not path.isfile(arg):
    parser.error("the file %s does not exist!"%arg)
  else:
    return open(arg, 'r')


def llvm2bpl(preludePath, libraryPath, infile):

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

  # find prelude and library paths
  scriptPathName = path.dirname(sys.argv[0])        
  scriptFullPath = path.abspath(scriptPathName)
  preludePath = path.join(scriptFullPath, 'prelude-int.bpl')
  libraryPath = path.join(path.dirname(scriptFullPath), 'lib', 'smack.so')


  # parse command line arguments
  parser = argparse.ArgumentParser(description='Outputs a Boogie file generated from the input LLVM file.')
  parser.add_argument('infile', metavar='<file>',
                      type=lambda x: is_valid_file(parser,x),
                      help='input LLVM file')
  parser.add_argument('-o', '--output', dest='outfile', metavar='<file>', default='a.bpl',
                      type=argparse.FileType('w'),
                      help='output Boogie file (default: %(default)s)')
  args = parser.parse_args()

  bplOutput = llvm2bpl(preludePath, libraryPath, args.infile)

  # write final output
  args.outfile.write(bplOutput)
  args.outfile.close()

