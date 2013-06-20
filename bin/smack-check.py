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
  parser.add_argument('-d', '--debug', dest='debug', action="store_true", default=False,
                      help='turn on debug info')
  parser.add_argument('--mem-mod', dest='memmod', choices=['flat', 'twodim'], default='flat',
                      help='set the memory model (flat=flat memory model, twodim=two dimensional memory model)')
  args = parser.parse_args()

  debug, bpl = llvm2bpl(path.dirname(sys.argv[0]), args.infile, args.debug, args.memmod)

  # print debug info
  if args.debug:
    print debug

  # put inline on procedures
  p = re.compile('procedure[ ]*([a-zA-Z0-9_]*)[ ]*\(')
  bpl = p.sub(lambda match: addInline(match), bpl)

  # write final output
  args.outfile.write(bpl)
  args.outfile.close()

  # invoke Boogie
  p = subprocess.Popen(['boogie', args.outfile.name, '/timeLimit:1200', '/loopUnroll:20'], stdout=subprocess.PIPE)
  boogieOutput = p.communicate()[0]
  print boogieOutput

