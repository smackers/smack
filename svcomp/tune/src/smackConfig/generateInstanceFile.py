#!/usr/bin/python

import sys
import glob
import os
from wrapperSmack import *
sys.dont_write_bytecode = True # prevent creation of .pyc files

dfltTimeout = 120
dfltArgs = ['--unroll', '12', '--verifier', 'boogie']

def getFileList(folder):
    #Ensure trailing slash
    folder = folder if folder[-1] == "/" else folder + "/"
    return sorted(glob.glob(folder + "*.c"))

def genInstanceFile(fileList, timeout=dfltTimeout, addArgs=dfltArgs):
    res = batchRunSmack(fileList, timeout, addArgs, showProgress=True)
    stats = getBatchStats(res)
    formattedStats = formatBatchStatSummary(stats)
    print(formattedStats)
    writeBatchFile('instanceStats.txt',formattedStats)
    return formatBatchFile(res)

if __name__ == '__main__':
    folder = sys.argv[1]
    instanceList = getFileList(folder)
    instFileString = genInstanceFile(instanceList)
    writeBatchFile('instanceSmack.txt', instFileString)
