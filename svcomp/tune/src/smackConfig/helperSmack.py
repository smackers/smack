#!/usr/bin/python

from __future__ import print_function
import sys
sys.dont_write_bytecode = True # prevent creation of .pyc files
import subprocess
from smackWrapper import *


#############################
### Batch execution functions
#############################

###Runs a tool on a list of files
def batchToolRun(fileList, timeout, addArgs, showProgress=False):
    res = []
    cnt = 0
    lastlength = 0
    #Collect results from each benchmark
    for inFile in fileList:
        toolRun = SmackToolRun(['',inFile,'',timeout,'-1','-1'] + addArgs)
        toolRun.executeRun()
        res.append(toolRun)
        if showProgress:
            cnt += 1
            msg = (str(cnt) + 
                   '/' + str(len(fileList)) + 
                   ' : ' + res[-1].inputFile +
                   ' ' + str(res[-1].runtime) +
                   ' ' + res[-1].outcome)
            #Clear the line (in case last one was longer)
            print(' '*lastlength, end='\r')
            print(msg, end='\r')
            lastlength = len(msg)
    if showProgress:
        print(' '*lastlength, end='\r')
    return res

###Generates stats on a batch run
def getBatchStats(resultList):
    satCnt = unsatCnt = timeoutCnt = totalTime = 0
    for result in resultList:
        if result.outcome == "CORRECT":
            satCnt += 1
        elif result.outcome == "WRONG":
            unsatCnt += 1
        elif result.outcome == "TIMEOUT":
            timeoutCnt += 1
        totalTime += result[1]
    return [satCnt, unsatCnt, timeoutCnt, totalTime]

###Formats stats from a batch run for printing
def formatBatchStatSummary(stats):
    (satCnt, unsatCnt, timeoutCnt, totalTime) = stats
    out =  "Summary:"
    out += "\n\tCORRECT Count:\t" + str(satCnt)
    out += "\n\tWRONG Count:\t" + str(unsatCnt)
    out += "\n\tTIMEOUT Count:\t" + str(timeoutCnt)
    out += "\n\tTotal Runtime:\t" + str(totalTime) + "\n"
    return out

###Formats a batch file for printing
def formatBatchFile(resultList, printSummary=False):
    toFile = []
    longestFile = longestFloat = 0
    for result in resultList:
        #track longest filename for printing alignment
        if len(result.inputFile) >= longestFile:
            longestFile = len(result.inputFile)
        if len(result.runtime) >= longestFloat:
            longestFloat = len(result.runtime)
    for result in resultList:
        #Align printing
        #Convert from list of lists to list of output lines
        toFile.append(result.inputFile + 
                      " "*(longestFile-len(result.inputFile)+1) + 
                      str(result.runtime) + 
                      " "*(longestFloat-len(str(result.runtime))+1) + 
                      result.outcome)
    ret = "\n".join(toFile)
    if printSummary:
        stats = getBatchStats(resultList)
        ret += formatBatchStatSummary(stats)
    return ret

###Writes a batch file (writes any string, really...)
def writeBatchFile(fileName, contents):
    with open(fileName, 'w') as instFile:
        instFile.write(contents)
