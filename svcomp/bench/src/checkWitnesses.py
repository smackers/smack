#!/usr/bin/env python

import xml.etree.ElementTree as ET
import os
import glob
import time
import subprocess
import re
import sys
sys.dont_write_bytecode = True # prevent creation of .pyc files

"""
This file takes an execution results directory as an argument, and generates a
list of all output xml results files.  For each output xml result file, it runs
cpachecker as a witness checker on each benchmark for which an error was found
(i.e., had a 'false' result).

The original output xml file is modified in memory to include results statuses
from the witness checker for each benchmark 'false' benchmark, as well as
enabling the witness related output file download links.

The modified in-memory output xml is then written as a new output xml file, with
the string ".witchecked" injected into the original output xml file name.  E.g.,
this file will write a file called "a.witchecked.Simple.xml" if it encounters an
original output xml file called "a.Simple.xml".
"""

if not 2 == len(sys.argv) or not os.path.isdir(sys.argv[1]):
    print
    print("Usage:\t" + sys.argv[0] + " EXECRESULTDIR")
    print
    print("EXECRESULTDIR\tA path to a directory containing a SMACKBench")
    print("\t\texecution result set, on which to check witnesses")
    exit()

execDir = os.getcwd()
targetDir = sys.argv[1]

targetDir = os.path.join(targetDir, 'results')
outXmls = glob.glob(targetDir + '/*results*.xml')

for outXml in outXmls:
    baseXml,setName = os.path.splitext(os.path.splitext(outXml)[0])
    outXmlNew = baseXml + '.witchecked' + setName + '.xml'
    tree = ET.parse(outXml)

    root = tree.getroot()
    runName = root.get('name')
    benchmarkName = root.get('benchmarkname')
    runDate = root.get('date')
    runDate = time.strptime(runDate, "%Y-%m-%d %H:%M:%S %Z")
    runDate = "{0:04d}-{1:02d}-{2:02d}_{3:02d}{4:02d}".format(runDate.tm_year,
                                                              runDate.tm_mon,
                                                              runDate.tm_mday,
                                                              runDate.tm_hour,
                                                              runDate.tm_min)
    runTimelimit = root.get('timelimit')
    witTimelimit = int(runTimelimit.split()[0])/10
    
    pathPrefix = benchmarkName + "." + runDate
    logFolder = os.path.join(targetDir, pathPrefix + ".logfiles")
    fileRoot = os.path.join(logFolder, runName)
    for run in root.findall('run'):
        sourcefile = run.get('name')
        # Get property file from input benchmark folder
        propfile = os.path.join(os.path.join('data', os.path.split(sourcefile)[0]), 'ALL.prp')
        # Now set sourcefile to where it WOULD be in output folders, 
        # given the folder structure of the actual input folder
        tokenizedInputFile = os.path.join('data', sourcefile)
        print(tokenizedInputFile)
        sourcefile = os.path.join(fileRoot,sourcefile)
        basefile = os.path.splitext(sourcefile)[0]

        witnessfile = sourcefile + '.witness.graphml'
        witnesscheckOutput = sourcefile + '.witnessCheckOutput'
        categoryCol = run.find('./column[@title="category"]')
        statusCol = run.find('./column[@title="status"]')
        outputfilesCol = run.find('./column[@title="Output Files"]')
        # Make sure columns existed (they don't when runSet was terminated early)
        if categoryCol is not None and statusCol is not None:
            category = categoryCol.get('value')
            status = statusCol.get('value')
            # We only need to witness check if we got the answer right
            # and the verification result was false
            if 'correct' in category and 'false' in status:
                # Use runexec to enforce time limit
                # cpachecker complains if working directory isn't the cpachecker
                # directory, so we have to adjust paths to match this requirement
                cmd  = ['../benchexec/bin/runexec']
                cmd += ['--output', '../' + witnesscheckOutput]
                cmd += ['--timelimit', str(witTimelimit)]
                cmd += ['--']
                # Below this point are the witness checking commands
                cmd += ['./scripts/cpa.sh']
                cmd += ['-noout']
                cmd += ['-heap', '16000M']
                cmd += ['-spec', '../' + witnessfile]
                cmd += ['-spec', '../' + propfile]
                cmd += ['../' + tokenizedInputFile]
                os.chdir('cpachecker')
                p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
                cmdOut = p.communicate()[0]
                checktime = float(re.search('cputime=(.*)s', cmdOut.decode('utf-8')).group(1))
                
                os.chdir(execDir)
                witSuccess = False
                witTimeout = False
                with open(witnesscheckOutput, 'r') as witout:
                    output = witout.read()
                    witSuccess = re.search('Verification result:\s*FALSE', output)
                    witTimeout = re.search('EDIT THIS WHEN YOU KNOW TIMEOUT STRING', output)
                if witSuccess:
                    statusCol.set('value','witness confirmed')
                else:
                    statusCol.set('value', 'something went wrong')
                if outputfilesCol is not None:
                    newVal = outputfilesCol.get('value').replace(' hidden','')
                    outputfilesCol.set('value', newVal)
                ET.SubElement(run, 'column', {'title':'time(s)\nfor\nwitness',
                                              'value':"{0:.3f}s".format(checktime)})
    tree.write(outXmlNew)
