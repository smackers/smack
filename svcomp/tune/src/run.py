#!/usr/bin/python

import sys
sys.dont_write_bytecode = True # prevent creation of .pyc files
import os
import multiprocessing
import subprocess
from argparse import *
from lib import generateBaseline

paramilsDir='paramils2.3.8-source'
paramilsExe='param_ils_2_3_run.rb'
scenariosFolder = './scenarios/'
scenarioFile = 'scenario.txt'

def parseArgs():
    
    p = ArgumentParser(description="Performs parameter tuning for the SMACK framework",
                       epilog="Performance evaluated based on speedup, so a baseline must " +
                       "be generated for any scenario prior to tuning")
    scenarios = listScenarios()
    procCount = multiprocessing.cpu_count()
    p.add_argument("--scenario",
                   help="The scenario to tune",
                   choices=scenarios,
                   required=True)
    p.add_argument("--phase",
                   help="The phase of SMACKTune to perform",
                   choices=['generateBaseline', 'tune', 'testSolution'],
                   required=True)
    p.add_argument("--concurrent-runs",
                   help="The number of concurrent calls to ParamILS " +
                   "(applies only to 'tune' phase)",
                   type=int,
                   choices=range(1,procCount+1),
                   default=1)
    args = p.parse_args()
    return args

def listScenarios():
    #Return immediate subdirectories of 'scenarios' folder
    return [x for x in os.walk(scenariosFolder)][0][1]
    
if __name__ == '__main__':
    args = parseArgs()
    if args.phase == "generateBaseline":
        generateBaseline.genInstanceFiles(os.path.join(scenariosFolder, args.scenario))
    elif args.phase == "tune":
        runs = list()
        for concurRun in range(args.concurrent_runs):
            scenarioDir = os.path.join(scenariosFolder, args.scenario)
            scenarioFilename = os.path.join(scenarioDir, scenarioFile)
            paramilsFullPath = os.path.join(paramilsDir, paramilsExe)
            cmd =  ['ruby']
            cmd += [os.path.relpath(paramilsFullPath, scenarioDir)]
            cmd += ['-numRun', str(concurRun)]
            cmd += ['-userunlog', '1']
            cmd += ['-validN', '1000']
            cmd += ['-pruning', '0']
            cmd += ['-scenariofile', scenarioFile]
            p = subprocess.Popen(cmd, cwd = os.path.join(scenariosFolder, args.scenario))
            runs.append(p)
        for run in runs:
            run.wait()
    elif args.phase == "testSolution":
        print("Not implemented")
        exit()

