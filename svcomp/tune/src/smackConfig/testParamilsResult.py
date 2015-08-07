#!/usr/bin/python

import sys
from helperSmack import *
sys.dont_write_bytecode = True # prevent creation of .pyc files

def getInstanceList(instanceFileFilename):
    with open(instanceFileFilename, 'r') as instFile:
        files = [line.split(' ')[0] for line in instFile]
    return files

def genResultTestFile(fileList, timeout, addArgs):
    res = batchRunSmack(fileList, timeout, addArgs, showProgress=True)
    stats = getBatchStats(res)
    print(formatBatchStatSummary(stats))
    return formatBatchFile(res, printSummary=True)

if __name__ == '__main__':
    #Args:
    #    0 - script name
    #    1 - instanceFile file
    #    2 - result file
    #    3 - output file
    instanceFileFilename = sys.argv[1]
    resultFilename = sys.argv[2]
    outputFilename = sys.argv[3]
    #Get result params & cutoff time
    resultantParams = getResultFileParams(resultFilename)
    cutoffTime = getResultFileCutoffTime(resultFilename)
    #Convert paramils formatted params to smack formatted params
    resultantParams = collectVerifierOptions(resultantParams)
    instanceList = getInstanceList(instanceFileFilename)
    rsltTestFileString = genResultTestFile(instanceList, cutoffTime, resultantParams)
    writeBatchFile(outputFilename, rsltTestFileString)
