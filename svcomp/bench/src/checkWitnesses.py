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

#execDir is folder containing this script, checkWitnesses.py
execDir = os.getcwd()
#targetDir is the run results folder we are trying to witness check
#(example data/runs/exec_2016.10.25._12.04.41.554365_WCTest)
targetDir = sys.argv[1]

#Append results folder to targetDir
#(example data/runs/exec_2016.10.25._12.04.41.554365_WCTest/results)
targetDir = os.path.join(targetDir, 'results')
#get a list of all results.xml files for this run
outXmls = glob.glob(targetDir + '/*results*.xml')

for outXml in outXmls:
    #The last token when splitting by "." is the set name
    #example file = svcomp_m32_witcheck.2016-10-25_1204.results.WCTest-WCTestDescription.WCTest.txt
    #The last field here (WCTest) is the set name (coming from the file WCTest.set)
    #The second to last field name is the set name + description, separated by a -
    baseXml,setName = os.path.splitext(os.path.splitext(outXml)[0])
    # skip certain sets
    if 'DeviceDriversLinux64' in setName or 'HeapReach' in setName or 'Concurrency' in setName:
      exit()
    #outXmlNew will be the new output xml file with the witnesschecked results,
    #leaveing the original file intact.
    outXmlNew = baseXml + '.witchecked' + setName + '.xml'
    tree = ET.parse(outXml)

    root = tree.getroot()
    #runName is the setname + description (WCTest-WCTestDescription)
    runName = root.get('name')
    #benchmarkname is the name of the input xml file, minus the extension
    #example = svcomp_m32_witcheck
    benchmarkName = root.get('benchmarkname')
    runDate = root.get('date')
    runDate = time.strptime(runDate, "%Y-%m-%d %H:%M:%S %Z")
    #Reformatted runDate example = 2016-10-25_1204
    runDate = "{0:04d}-{1:02d}-{2:02d}_{3:02d}{4:02d}".format(runDate.tm_year,
                                                              runDate.tm_mon,
                                                              runDate.tm_mday,
                                                              runDate.tm_hour,
                                                              runDate.tm_min)
    runTimelimit = root.get('timelimit')
    #witness checking timelimit should be 10% of time limit for tool to solve
    witTimelimit = int(runTimelimit.split()[0].replace("s",""))/10
    
    #pathPrefix example = svcomp_m32_witcheck.2016-10-25_1204
    pathPrefix = benchmarkName + "." + runDate
    #logFolder example =
    #../data/runs/exec_2016.10.25_12.04.41.554365_WCTest/results/svcomp_m32_witcheck.2016-10-25_1204.logfiles/
    logFolder = os.path.join(targetDir, pathPrefix + ".logfiles")
    #Loop through each benchmark file in the run
    for run in root.findall('run'):
        #sourcefile is input *.c or *.i file (including path)
        sourcefile = run.get('name')
        # Get property file from input benchmark folder
        propfile = os.path.join(os.path.join('data', os.path.split(os.path.split(sourcefile)[0])[0]), 'PropertyUnreachCall.prp')
        #split the sourcefile into its svcomp source path, and the actual filename
        #(that is, get rid of the original source path)
        _,targetfile = os.path.split(sourcefile)
        targetfile = os.path.join(logFolder, runName + "." + targetfile)

        #Get the input and output witness checking file names
        witnessfile = targetfile + '.witness.graphml'
        #benchexecWitnesscheckOutput will be the console output of whatever witness checking
        #tool gets executed (currently the cpachecker web validator).  This file will contain
        #the running time for the cpachecker web validator.
        benchexecWitnesscheckOutput = targetfile + '.witnessCheckOutput'
        #webValidatorWitnesscheckOutput will be the log file written by the cpachecker web
        #validator.  This file will contain the witness checking outcome, such as FALSE, TRUE,
        # or TIMEOUT
        webValidatorWitnesscheckOutput = targetfile + 'output.log'
        categoryCol = run.find('./column[@title="category"]')
        statusCol = run.find('./column[@title="status"]')
        outputfilesCol = run.find('./column[@title="Output Files"]')
        # Make sure columns existed (they don't when runSet was terminated early)
        if categoryCol is not None and statusCol is not None:
            category = categoryCol.get('value')
            status = statusCol.get('value')
            # We only need to witness check if we got the answer right
            # and the verification result was false
            #if 'correct' in category and 'false' in status:
            correct = None
            if 'false' in status:
              correct = False
            elif 'true' in status:
              correct = True
            if correct is not None and os.path.isfile(witnessfile):
                # Use runexec to enforce time limit
                # cpachecker complains if working directory isn't the cpachecker
                # directory, so we have to adjust paths to match this requirement
                cmd  = ['../../benchexec/bin/runexec']
                cmd += ['--output',  '../../' + benchexecWitnesscheckOutput]
                #cmd += ['--output',  benchexecWitnesscheckOutput]
                #cmd  = ['./benchexec/bin/runexec']
                #cmd += ['--output', benchexecWitnesscheckOutput]
                cmd += ['--timelimit', str(witTimelimit)]
                cmd += ['--']
                # Below this point are the witness checking commands
                cmd += ['./scripts/cpa.sh']
                ##### Simple CPAchecker Args
                if correct:
                  cmd += ['-correctness-witness-validation']
                  cmd += ['-setprop', 'invariantGeneration.kInduction.invariantsAutomatonFile='+os.path.abspath(witnessfile)]
                else:
                  cmd += ['-violation-witness-validation']
                  cmd += ['-spec', os.path.abspath(witnessfile)]
                cmd += ['-spec', os.path.abspath(propfile)]
                cmd += [os.path.abspath('data/' + sourcefile)]
                cmd += ['-outputpath', os.path.abspath( targetfile)]

                ##### Complex CPAchecker Args
                #cmd += ['-noout']
                #cmd += ['-heap', '16000M']
                #cmd += ['-witness-check']
                #cmd += ['-spec', '../' + witnessfile]
                #cmd += ['-spec', '../' + propfile]
                #cmd += ['../' + sourcefile]
                #os.chdir('cpachecker/CPAchecker-1.6.1-unix')
                os.chdir('cpachecker/cpachecker')

                #cmd += ['./witness_validation_web_cloud.py']
                #cmd += ['--program', "../data/" + sourcefile]
                #cmd += ['--witness', "../" + witnessfile]
                #cmd += ['-o', "../" + targetfile]
                p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
                
                #This console output (p.communicate()[0]) is ignored, and is only called to
                #block execution until the web validator finishes running.  The console output
                #here will contain the running time for the web validator script only, not the
                #actual running time of the validation, so it gets ignored.
                cmdOut = p.communicate()[0]
                #print(cmdOut.decode('utf-8'))
                #checktime = float(re.search('cputime=(.*)s', cmdOut.decode('utf-8')).group(1))
                os.chdir(execDir)
                #cmdOut = ""
                with open(benchexecWitnesscheckOutput,"r") as f:
                    output = f.read()
                print(cmdOut)
                checktime = float(re.search('cputime=(.*)s', cmdOut).group(1)) + 10

                witSuccess = False
                witTimeout = False
                #with open(webValidatorWitnesscheckOutput, 'r') as witout:
                #    output = witout.read()
                witSuccess = re.search('Verification result:\s*FALSE', output) if not correct else re.search('Verification result: TRUE.*', output)
                witTimeout = re.search('Verification result: UNKNOWN, incomplete analysis.', output)
                witFailure = re.search('Verification result: TRUE.*', output) if not correct else re.search('Verification result:\s*FALSE', output)
                if witSuccess:
                    statusCol.set('value','witness confirmed')
                else:
                    if witTimeout:
                        statusCol.set('value', 'witness timeout')
                        categoryCol.set('value', 'error')
                    else:
                        if witFailure:
                            statusCol.set('value', 'witness unconfirmed')
                            categoryCol.set('value', 'error')
                        else:
                            statusCol.set('value', 'something went wrong')
                            categoryCol.set('value', 'unknown')
                if outputfilesCol is not None:
                    newVal = outputfilesCol.get('value').replace(' hidden','')
                    outputfilesCol.set('value', newVal)
                ET.SubElement(run, 'column', {'title':'time(s)\nfor\nwitness',
                                              'value':"{0:.3f}s".format(checktime)})
                tree.write(outXmlNew)
