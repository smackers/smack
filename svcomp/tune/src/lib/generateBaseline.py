#!/usr/bin/python

import sys
sys.dont_write_bytecode = True # prevent creation of .pyc files
import glob
import os
from helperSmack import *

dfltArgsFile = 'defaultArgs.txt'
benchmarkFolder = 'benchmarks'
instanceStatsFile = 'instanceStats.txt'
instanceFile = 'instance.txt'

def getDefaultArgs(dfltArgFile):
    dfltArgs = list()
    dfltTimeout = None
    with open(dfltArgFile, 'r') as f:
        lines = f.readlines()
    for line in lines:
        if line.strip() == '' or line[0] == "#":
            #This is empty or a comment - do nothing
            continue
        tokens = line.split()
        if tokens[0] == 'timeout' or tokens[0] == 'Timeout':
            dfltTimeout = tokens[1]
        else:
            dfltArgs.append('-' + tokens[0])
            dfltArgs.append(tokens[1])
    if dfltTimeout is None:
        raise "Default args file must define 'Timeout' value"
    return dfltTimeout, dfltArgs
        

def getFileList(scenarioFolder, benchmarkDir):
    #Ensure trailing slash
    oldcwd = os.getcwd()
    os.chdir(scenarioFolder)
    benchmarkDir = benchmarkDir if benchmarkDir[-1] == "/" else benchmarkDir + "/"
    fileList = sorted(glob.glob(benchmarkDir + "*.c"))
    os.chdir(oldcwd)
    return fileList

def genInstanceFiles(scenarioFolder):
    timeout, addArgs = getDefaultArgs(os.path.join(scenarioFolder, dfltArgsFile))
    fileList = getFileList(scenarioFolder, benchmarkFolder)
    res = batchToolRun(scenarioFolder, fileList, timeout, addArgs, showProgress=True)
    stats = getBatchStats(res)
    formattedStats = formatBatchStatSummary(stats)
    print(formattedStats)
    writeBatchFile(os.path.join(scenarioFolder, instanceStatsFile),
                   formattedStats)
    writeBatchFile(os.path.join(scenarioFolder, instanceFile),
                   formatBatchFile(res))
