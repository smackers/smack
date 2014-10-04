#!/usr/bin/env python
#
# This file is distributed under the MIT License. See LICENSE for details.
#

import argparse
import re
import pprint
import subprocess
import json
from smackgen import *
from smackverify import *

VERSION = '1.4.1'

def reachParser():
    parser = argparse.ArgumentParser(add_help=False, parents=[verifyParser()])
    
    return parser

# File line numbers are 0-based idx
def CopyFileWhileInserting(srcFile, dstFile, lineNumber, insertText):
    inFile = open(srcFile, "r")
    inContents = inFile.readlines()
    inFile.close()

    if(not insertText.endswith('\n')):
        insertText += '\n'

    inContents.insert(lineNumber, insertText)

    outFile = open(dstFile, "w")
    outFile.write("".join(inContents))
    outFile.close()

# Each item in return value is [fileName, sourceLineNo, bplLineNo, isReachable]
def GetSourceLineInfo(bplFile):
    FILENAME = '[\w#$~%.\/-]+'
    regex = '.*{:sourceloc \"(' + FILENAME + ')\", (\d+), (\d+)}.*'
    sourcelocRe = re.compile(regex)

    sourceInfo = []

    bplCount = 0;

    with open(bplFile) as inFile:
        for line in inFile.readlines():
            #Groups: 1=filename, 2=sourceLineNo, 3=sourceColNo
            match = sourcelocRe.match(line)
            if(match):
                newSource = {
                    'filename' : match.group(1),
                    'sourceLineNo' : int(match.group(2)),
                    'sourceColNo' : int(match.group(3)),
                    'bplLineNo' : bplCount,
                    'isReachable' : False
                    }
                sourceInfo.append(newSource)
            bplCount += 1
    
    return sorted(sourceInfo, key=lambda e:e['sourceLineNo'], reverse=True)

def UpdateWithClangInfo(clangOuptut, sourceInfo):
    FILENAME = '[\w#$~%.\/-]+'
    regex = '(' + FILENAME + '):(\d+):(\d+): warning: will never be executed \[-Wunreachable-code\]'
    clangFilter = re.compile(regex)

    for line in clangOutput.splitlines(True):
        match = clangFilter.match(line)
        if(match):
            newSource = {
                'filename' : match.group(1),
                'sourceLineNo' : int(match.group(2)),
                'sourceColNo' : int(match.group(3)),
                'bplLineNo' : -1,
                'isReachable' : False
                }
            sourceInfo.append(newSource)

def GetCodeCoverage(verifier, bplFileName, timeLimit, unroll, debug, smackd, clangOutput):
    sourceInfo = GetSourceLineInfo(bplFileName)

    for sourceLine in sourceInfo:
        if(not sourceLine['isReachable']):
            reachRes = TestReachability(verifier, bplFileName, timeLimit, unroll, debug, sourceLine)

            #TODO - how does python handle changing lists in for loop?
            UpdateSourceInfo(reachRes, sourceInfo, verifier)

    #Add lines caught by clang's -Wunreachable-code
    UpdateWithClangInfo(clangOutput, sourceInfo)
            
    # Extract info
    result = {}
    for sourceLine in sourceInfo:
        if(not sourceLine["isReachable"]):
            if(not sourceLine["filename"] in result):
                result[sourceLine["filename"]] = set()
            resItem = sourceLine["sourceLineNo"], sourceLine["sourceColNo"]
            result[sourceLine["filename"]].add(resItem)
    
    for curfile in result:
        #secondary sort by column
        result[curfile] = sorted(result[curfile], key=lambda e:e[1], reverse=False)
        #primary sort by line
        result[curfile] = sorted(result[curfile], key=lambda e:e[0], reverse=False)

    if(smackd):
        print(json.dumps(result))
    else:
        print '\nSMACK verifier version ' + VERSION + '\n\n'
        print "Unreachable code:"
        pprint.pprint(result, width=100)

def TestReachability(verifier, bplFileName, timeLimit, unroll, debug, lineInfo):
    boogieText = "assert false;"

    bplfileBase = path.splitext(bplFileName)[0]
    bplNew = bplfileBase + "_coverage.bpl"

    CopyFileWhileInserting(bplFileName, bplNew, lineInfo['bplLineNo'] + 1, boogieText)

    #do not pass smackd flag as true.  Breaks parsing
    corralOutput = verify(verifier, bplNew, timeLimit, unroll, debug, False)
    
    return corralOutput

def UpdateSourceInfo(corralOutput, sourceInfo, verifier):
    FILENAME = '[\w#$~%.\/-]+'
    regex = ""
    if(verifier == "corral"):
        regex = '(' + FILENAME + ')\((\d+),(\d+)\): Trace:.*'
    else:
        #boogie...
        #TODO Once line numbers are fixed for boogie-inline,
        #     we can save time here by using all traces,
        #     not just the instruction causing the failure
        #     (use trace that led to failing instruction, also)
        #  As is, current smackverify output using boogie-inline
        #     is including unvisited lines in traces. (See
        #     src/test/reach/switch.c)
        regex = '\s*(' + FILENAME + ')\((\d+),(\d+)\): Error.*'
    traceFilter = re.compile(regex)

    for line in corralOutput.splitlines(True):
        match = traceFilter.match(line)
        if(match):
            reachedLine = {
                'filename' : match.group(1),
                'sourceLineNo' : int(match.group(2)),
                # Corral adds one to column count
                'sourceColNo' : int(match.group(3)),
                }
            #run through each sourceInfo, if matches, set as reachable
            for sourceLine in sourceInfo:
                if     ((not sourceLine['isReachable']) and
                        reachedLine['filename'] == sourceLine['filename'] and 
                        reachedLine['sourceLineNo'] == sourceLine['sourceLineNo'] and 
                        reachedLine['sourceColNo'] == sourceLine['sourceColNo']):
                    sourceLine['isReachable'] = True


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description='Checks the input LLVM file for code reachability.', parents=[reachParser()])
    parser.parse_args() # just check if arguments are looking good

    #!!!!!!START COPY OF SECTION FROM smackverify.py!!!!!!!!!!!
    #  Probably should pull into subroutine or something
    # remove arguments not recognized by lower scripts
    # not sure of a better way to do this
    sysArgv = sys.argv[:]
    for i in reversed(range(len(sysArgv))):
        if sysArgv[i] == '--smackd':
            del sysArgv[i]
        elif sys.argv[i] == '--time-limit':
            del sysArgv[i]
            del sysArgv[i]


    #Add clang's -Wunreachable-code flag
    sysArgv.append('--clang=-Wunreachable-code')
    bpl, options, clangOutput = smackGenerate(sysArgv)
    args = parser.parse_args(options + sys.argv[1:])

    # write final output
    args.outfile.write(bpl)
    args.outfile.close()
    #!!!!!!END COPY OF SECTION FROM smackverify.py!!!!!!!!!!!

    GetCodeCoverage(args.verifier, args.outfile.name, args.timeLimit, args.unroll, args.debug, args.smackd, clangOutput)
