#!/usr/bin/env python
#
# This file is distributed under the MIT License. See LICENSE for details.
#

from os import path
import json
import sys
import re
import subprocess
import argparse
import platform
from smackgen import *

VERSION = '1.4.1'

def verifyParser():
  # parse command line arguments
  parser = argparse.ArgumentParser(add_help=False, parents=[smackParser()])

  parser.add_argument('--time-limit', metavar='N', dest='timeLimit', default='1200', type=int,
                      help='Boogie time limit in seconds')
  parser.add_argument('--smackd', dest='smackd', action="store_true", default=False,
                      help='output JSON format for SMACKd')
  return parser


def generateSourceErrorTrace(boogieOutput, bplFileName):
  FILENAME = '[\w#$~%.\/-]+'
  LABEL = '[\w$]+'

  bplFile = open(bplFileName)
  bpl = bplFile.read()
  bplFile.close()

  if not re.search('.*{:sourceloc \"(' + FILENAME + ')\", (\d+), (\d+)}.*', bpl):
    # no debug info in bpl file
    return None

  sourceTrace = '\nSMACK verifier version ' + VERSION + '\n\n'
  for traceLine in boogieOutput.splitlines(True):
    resultMatch = re.match('Boogie .* (\d+) verified, (\d+) error.*', traceLine)
    traceMatch = re.match('([ ]+)(' + FILENAME + ')\((\d+),(\d+)\): (' + LABEL + ')', traceLine)
    errorMatch = re.match('(' + FILENAME + ')\((\d+),(\d+)\): (.*)', traceLine)
    if resultMatch:
      verified = int(resultMatch.group(1))
      errors = int(resultMatch.group(2))
      sourceTrace += '\nFinished with ' + str(verified) + ' verified, ' + str(errors) + ' errors\n'
    elif traceMatch:
      spaces = str(traceMatch.group(1))
      filename = str(traceMatch.group(2))
      lineno = int(traceMatch.group(3))
      colno = int(traceMatch.group(4))
      label = str(traceMatch.group(5))

      for bplLine in bpl.splitlines(True)[lineno:lineno+10]:
        m = re.match('.*{:sourceloc \"(' + FILENAME + ')\", (\d+), (\d+)}.*', bplLine)
        if m:
          filename = str(m.group(1))
          lineno = int(m.group(2))
          colno = int(m.group(3))
 
          sourceTrace += spaces + filename + '(' + str(lineno) + ',' + str(colno) + ')\n'
          break
    elif errorMatch:
      filename = str(errorMatch.group(1))
      lineno = int(errorMatch.group(2))
      colno = int(errorMatch.group(3))
      message = str(errorMatch.group(4))
 
      for bplLine in bpl.splitlines(True)[lineno-2:lineno+8]:
        m = re.match('.*{:sourceloc \"(' + FILENAME + ')\", (\d+), (\d+)}.*', bplLine)
        if m:
          filename = str(m.group(1))
          lineno = int(m.group(2))
          colno = int(m.group(3))
 
          sourceTrace += filename + '(' + str(lineno) + ',' + str(colno) + '): ' + message + '\n'
          break
  return sourceTrace

 
def smackdOutput(corralOutput):
  FILENAME = '[\w#$~%.\/-]+'

  passedMatch = re.search('Program has no bugs', corralOutput)
  if passedMatch:
    json_data = {
      'verifier': 'corral',
      'passed?': True
    }

  else:
    traces = []
    for traceLine in corralOutput.splitlines(True):
      traceMatch = re.match('(' + FILENAME + ')\((\d+),(\d+)\): Trace: Thread=(\d+)  (\((.*)\))?$', traceLine)
      errorMatch = re.match('(' + FILENAME + ')\((\d+),(\d+)\): (error .*)$', traceLine)
      if traceMatch:
        filename = str(traceMatch.group(1))
        lineno = int(traceMatch.group(2))
        colno = int(traceMatch.group(3))
        threadid = int(traceMatch.group(4))
        desc = str(traceMatch.group(6))
        trace = { 'threadid': threadid, 'file': filename, 'line': lineno, 'column': colno, 'description': '' if desc == 'None' else desc }
        traces.append(trace)
      elif errorMatch:
        filename = str(errorMatch.group(1))
        lineno = int(errorMatch.group(2))
        colno = int(errorMatch.group(3))
        desc = str(errorMatch.group(4))
        failsAt = { 'file': filename, 'line': lineno, 'column': colno, 'description': desc }

    json_data = {
      'verifier': 'corral',
      'passed?': False,
      'failsAt': failsAt,
      'threadCount': 1,
      'traces': traces
    }
  json_string = json.dumps(json_data)
  print json_string

def verify(verifier, bplFileName, timeLimit, unroll, debug, smackd):
  if verifier == 'boogie':
    # invoke Boogie
    boogieCommand = ['boogie', bplFileName, '/nologo', '/timeLimit:' + str(timeLimit)]
    if unroll is not None:
      boogieCommand += ['/loopUnroll:' + str(unroll)]
    p = subprocess.Popen(boogieCommand, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    boogieOutput = p.communicate()[0]

    if p.returncode:
      print >> sys.stderr, boogieOutput
      sys.exit("SMACK encountered an error when invoking Boogie. Exiting...")
    if debug:
      return boogieOutput
    sourceTrace = generateSourceErrorTrace(boogieOutput, bplFileName)
    if sourceTrace:
      return sourceTrace
    else:
      return boogieOutput
  elif verifier == 'corral':
    # invoke Corral
    corralCommand = ['corral', bplFileName, '/tryCTrace']
    if unroll is not None:
      corralCommand += ['/recursionBound:' + str(unroll)]
    p = subprocess.Popen(corralCommand, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    corralOutput = p.communicate()[0]

    if p.returncode:
      print >> sys.stderr, corralOutput
      sys.exit("SMACK encountered an error when invoking Corral. Exiting...")
    if smackd:
      smackdOutput(corralOutput)
    else:
      return corralOutput
  else:
    # invoke Duality
    dualityCommand = ['corral', bplFileName, '/tryCTrace', '/useDuality']
    dualityCommand += ['/recursionBound:10000'] # hack for providing infinite recursion bound
    p = subprocess.Popen(dualityCommand, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    dualityOutput = p.communicate()[0]

    if p.returncode:
      print >> sys.stderr, dualityOutput
      sys.exit("SMACK encountered an error when invoking Duality. Exiting...")
    if smackd:
      smackdOutput(dualityOutput)
    else:
      return dualityOutput
 
if __name__ == '__main__':
  parser = argparse.ArgumentParser(description='Checks the input LLVM file for assertion violations.', parents=[verifyParser()])
  parser.parse_args() # just check if arguments are looking good

  # remove arguments not recognized by lower scripts
  # not sure of a better way to do this
  sysArgv = sys.argv[:]
  for i in reversed(range(len(sysArgv))):
    if sysArgv[i] == '--smackd':
      del sysArgv[i]
    elif sysArgv[i] == '--time-limit':
      del sysArgv[i]
      del sysArgv[i]

  bpl, options, clangOutput = smackGenerate(sysArgv)
  args = parser.parse_args(options + sys.argv[1:])

  # write final output
  with open(args.outfile, 'w') as outputFile:
    outputFile.write(bpl)
    outputFile.close()

  print(verify(args.verifier, args.outfile, args.timeLimit, args.unroll, args.debug, args.smackd))

