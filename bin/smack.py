#! /usr/bin/env python

from os import path
import sys
import subprocess
import argparse
from llvm2bpl import *

boogie = ['mono', '/home/zvonimir/projects/boogie/Binaries/Boogie.exe']


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

  # invoke Boogie
  p = subprocess.Popen(boogie + [args.outfile.name, '/timeLimit:1200', '/loopUnroll:15'], stdout=subprocess.PIPE)
  boogieOutput = p.communicate()[0]
  print boogieOutput

