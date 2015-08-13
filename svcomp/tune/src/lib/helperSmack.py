#!/usr/bin/python

from __future__ import print_function
import sys
sys.dont_write_bytecode = True # prevent creation of .pyc files
import subprocess
import time


#############################
### Batch execution functions
#############################

###Runs a tool on a list of files
def batchToolRun(execDir, tool, fileList, timeout, addArgs, showProgress=False):
    res = []
    cnt = 0
    lastlength = 0
    #Collect results from each benchmark
    for inFile in fileList:
        cmd = [tool]
        cmd += [inFile]
        cmd += ['']
        cmd += [str(timeout)]
        cmd += ['-1']
        cmd += ['-1']
        cmd += addArgs
        p = subprocess.Popen(cmd, cwd=execDir, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        out,err = p.communicate()
        curRes = object()
        for line in out.splitlines():
            m = re.match(r'Results for ParamILS: (.*), (.*), (.*), (.*), (.*)', line)
            if m:
                curRes.inputFile = inFile
                curRes.outcome = m.group(1)
                curRes.runtime = m.group(2)
                curRes.runlength = m.group(3)
                curRes.best_sol = m.group(4)
                curRes.seed = m.group(5)
        res.append(curRes)
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
            sys.stdout.flush()
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
        totalTime += result.runtime
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
        if len(str(result.runtime)) >= longestFloat:
            longestFloat = len(str(result.runtime))
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
