#! /usr/bin/env python

from os import path
import sys
import re
import subprocess
import argparse
import platform
from llvm2bpl import *


def addInline(match):
  procName = match.group(1)
  procDef = ''
  if procName == 'main':
    procDef += 'procedure ' + procName + '('
  else:
    procDef += 'procedure {:inline 1} ' + procName + '('
  return procDef


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


  # put inline on procedures
  p = re.compile('procedure[ ]*([a-zA-Z0-9_]*)[ ]*\(')
  bplOutput = p.sub(lambda match: addInline(match), bplOutput)


  # write final output
  args.outfile.write(bplOutput)
  args.outfile.close()

  # invoke Boogie
  p = subprocess.Popen(['boogie', args.outfile.name, '/timeLimit:1200', '/loopUnroll:20'], stdout=subprocess.PIPE)
  boogieOutput = p.communicate()[0]
  print boogieOutput

