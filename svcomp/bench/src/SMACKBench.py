#!/usr/bin/env python
import sys
sys.dont_write_bytecode = True # prevent creation of .pyc files

import argparse
import daemon
import json
import os
import signal
import subprocess
import sys
import time
from datetime import datetime
from os import path
from socket import gethostname

#######################################
###  Common functions
#######################################
def get_args():
    parser = argparse.ArgumentParser(description='Executes a SMACKBench jobs queue')
    subparsers = parser.add_subparsers(help = 'Sub-command help')
    server = subparsers.add_parser('server',
                                   help = 'Start SMACKBench in server mode',
                                   formatter_class=argparse.ArgumentDefaultsHelpFormatter)
    server.set_defaults(mode='server')
    server.add_argument('-q', '--queue-file',
                        default='inputFiles/queue', metavar='FILE',
                        help='The file containing the list of jobs to process')
    server.add_argument('-r', '--concurrentRuns',
                        default='8', metavar='NUM',
                        help='The number of concurrent benchmarks to run')
    server.add_argument('-m', '--memoryPerRun',
                        default='15000', metavar='NUM',
                        help='Amount of memory per concurrent run (in MB)')
    server.add_argument('-c', '--config-file',
                        default='inputFiles/config.json', metavar='FILE',
                        help='The json file with SMACKBench config settings')
    server.add_argument('-d', '--description',
                        default='', metavar='DESC',
                        help='A description field (identifier) to be associated with each set')

    stop = subparsers.add_parser('stop',
                                 help='Stop all instances of SMACKBench')
    stop.set_defaults(mode='stop')

    run = subparsers.add_parser('run',
                                help='Run SMACKBench on a single svcomp set',
                                formatter_class=argparse.ArgumentDefaultsHelpFormatter)
    run.set_defaults(mode='run')
    run.add_argument('-s', '--svcomp-set', required=True, metavar='SET',
                     help='The svcomp set to execute')
    run.add_argument('-x', '--inputXmlFile', required=True, metavar='FILE',
                     help='The input XML file with which to run svcomp-set')
    run.add_argument('-r', '--concurrentRuns', default='8', metavar='NUM',
                     help='The number of concurrent benchmarks to run')
    run.add_argument('-m', '--memoryPerRun', default='15000', metavar='NUM',
                     help='Amount of memory per concurrent run (in MB)')
    run.add_argument('-c', '--config-file',
                     default='inputFiles/config.json', metavar='FILE',
                     help='The json file with SMACKBench config settings')
    run.add_argument('-d', '--description',
                     default='', metavar='DESC',
                     help='A description field (identifier) to be associated with each set')
    args = parser.parse_args()
    return args

def get_config(configFile):
    with open(configFile, 'r') as f:
        cfg = json.load(f)
    return cfg

def handle_sigterm(signum, frame):
    #benchexec only runs cleanup routine when it sees
    #sigint.  To force this to run when receiving a sigterm,
    #we'll intercept it and simulate a sigint instead
    raise KeyboardInterrupt

#######################################
##                                   ##
## SMACKBenchServer                  ##
##                                   ##
#######################################

#######################################
###  SMACKBench Queueing functions
#######################################

#Creates a lock by making the directory lock_dir (in cwd)
#If directory exists, lock is already being held
def lock(lock_dir):
    while True:
        try:
            os.mkdir(lock_dir)
            return
        except OSError as e:
            if e.errno != 17:
                raise

#Releases a lock by deleting the directory lock_dir (from cwd)
def unlock(lock_dir):
    try:
        os.rmdir(lock_dir)
    except:
        pass

def dequeue(filename, lock_folder):
    #Pops and returns a line off the top of the input file
    try:
        cur = None
        lock(lock_folder)
        with open(filename,'r+') as f:
            lines = f.readlines()
            f.seek(0)
            if len(lines)==0:
                unlock(lock_folder)
                return cur
            cur = lines[0].strip()
            lines = lines[1:]
            for line in lines:
                f.write(line)
            f.truncate()
    finally:
        unlock(lock_folder)
    return cur

def enqueue(data, filename, lock_folder):
    #Pushes a line to the end of the given filename
    #(I think this is currently unused)
    try:
        lock(lock_folder)
        with open(filename,'a') as f:
            f.write(data + '\n')
    finally:
        unlock(lock_folder)

#######################################
###  SMACKBench Server 
#######################################
def run_server(cfgObj, queueFile, concurRunCnt, memPerRun, desc):
    #Register our sigterm handler, so we can catch it and raise
    #KeyboardInterrupt instead.  This way benchexec's cleanup
    #routines run
    signal.signal(signal.SIGTERM, handle_sigterm)
    lock_folder = 'lck'
    while(True):
        # Pop a job
        job = dequeue(queueFile, lock_folder)
        # And run it if it exists (that is, if the queue is not empty)
        if job:
            # First, clean old .bc, .bpl, and .ll
            # Deletes files modified more than 2 hours
            cmdPre = ['find', './', '-maxdepth', '1', '-name']
            cmdPost = ['-mmin', '+120', '-delete']
            for ext in ['bpl','bc','ll','i','c','dot']:
                subprocess.call(cmdPre + ['"*.' + ext + '"'] + cmdPost);
            
            job = job.split() #Splits into [<svSet>, <inXmlFile>]
            runSMACKBench(cfgObj, job[0], job[1], concurRunCnt, memPerRun, desc)
        else:
            #If the queue file is empty, wait 10 seconds
            time.sleep(10)

#######################################
##                                   ##
## runSMACKBench                     ##
##                                   ##
#######################################
def generateOutFolder(cfgObj, svSet):
    #Generate output folder name and create new directory
    timestamp = datetime.now().strftime("%Y.%m.%d_%H.%M.%S.%f")
    outFold = "exec_{0}_{1}".format(timestamp,svSet)
    outPath = path.join(cfgObj['runsFolder'], outFold)
    os.makedirs(outPath)
    return outPath

def copyInXmlAndInject(cfgObj, outPath, svSet, inXmlFile, memPerRun, desc):
    #Deterime the destination input xml file location
    dstInXmlFile = path.join(outPath, path.split(inXmlFile)[-1])
    #Read the input xml file template (must use .. since input xml
    #  file is relative to root, but we changed cwd to dataFolder,
    #  so we must adjust this path)
    with open(path.join('..', inXmlFile), 'r') as inXml:
        inXmlStr = inXml.read()
    #NOTE: Replacement variables in input xml template that begin
    #      with a $ are used by benchexec (e.g., ${sourcefile_path})
    #      Replacement vars in use by SMACKBench take the form {varname}
    #Inject set name
    inXmlStr = inXmlStr.replace('{SETNAME}', svSet)
    #Inject description (we hijack the benchexec setdefinition_name field to 
    #  contain description.  This allows us to avoid changing xml schema of 
    #  benchexec in/out xml files.)
    inXmlStr = inXmlStr.replace('{DESCRIPTION}', 
                                '' if not desc else '-'+desc.replace(' ',''))
    #Inject memory per concurrent run limit
    inXmlStr = inXmlStr.replace('{MEMLIMIT}', memPerRun)
    #Inject number of cores allowed for each concurrently run benchmark
    inXmlStr = inXmlStr.replace('{CORELIMIT}', cfgObj['coreLimit'])
    #Determine the set definition file, relative to the dest input xml file
    bmRel = path.relpath(cfgObj['benchmarkRoot'], path.dirname(dstInXmlFile))
    setDefFile = path.join(bmRel, svSet + ".set")
    prpDefFile = path.join(bmRel, svSet + ".prp")
    #Inject the set definition file (*.set) path (using relative path)
    #  (benchexec does everything relative to the input xml file)
    inXmlStr = inXmlStr.replace('{SETDEFINITIONFILE}', setDefFile)
    inXmlStr = inXmlStr.replace('{PROPERTYDEFINITIONFILE}', prpDefFile)

    #Write the input xml file
    with open(dstInXmlFile, 'w') as dstXml:
        dstXml.write(inXmlStr)
    #Return the full file path of the injected input xml file
    return dstInXmlFile

def runBenchExec(cfgObj, inXmlFile, outPath, concurRunCnt, debug):
    #This should probably be changed to use the benchexec python modules,
    #  rather than running as an executable
    
    #Config file passes benchexecPath as relative to root, but we changed
    #  cwd to dataFolder, and reference everything from this folder.  As
    #  a result, we must patch the benchexecPath so it is relative to 
    #  dataFolder
    cmd =  [path.join('..', cfgObj['benchexecPath'], 'benchexec')]
    if debug:
        cmd += ['-d']
    cmd += [inXmlFile]
    #For some reason, benchexec needs to see a / on the end of the string
    #  to know the last item of the -o value is a folder.
    cmd += ['-o', path.join(outPath, 'results') + '/']
    cmd += ['--no-compress']
    cmd += ['-N', concurRunCnt]

    print(cmd)
    p = subprocess.Popen(cmd)
    try:
        p.wait()
    except KeyboardInterrupt as e:
        #If we get interrupted by a KeyboardInterrupt, pass it on to
        #  benchexec, so it can do its cleanup
        p.send_signal(signal.SIGINT)
        raise KeyboardInterrupt

def witnessCheckingFunc(cfgObj, outPath):
    #Get cwd, so we can return afterwards
    execDir = os.getcwd()
    print(execDir)
    #change to root dir
    os.chdir('..')
    print(os.getcwd())
    cmd =  ['./checkWitnesses.py']
    cmd += [os.path.join(cfgObj["dataFolder"], outPath)]
    print(cmd)
    p = subprocess.Popen(cmd)
    try:
        p.wait()
    except KeyboardInterrupt as e:
        #If we get interrupted by a KeyboardInterrupt, pass it on to
        #  benchexec, so it can do its cleanup
        p.send_signal(signal.SIGINT)
        raise KeyboardInterrupt
    os.chdir(execDir)
        
def runSMACKBench(cfgObj, svSet, inXmlFile, concurRunCnt, memPerRun, desc):
    #Generate results folder name and create
    outPath = generateOutFolder(cfgObj, svSet)
    #Copy the input xml file template to the new output directory,
    # and inject relevant variables
    dstInXml = copyInXmlAndInject(cfgObj, outPath, svSet, inXmlFile, memPerRun, desc)
    #Call benchexec
    runBenchExec(cfgObj, dstInXml, outPath, concurRunCnt, debug = False)
    #Run witness checking
    witnessCheckingFunc(cfgObj, outPath)

if __name__ == '__main__':
    args = get_args()
    #If stop command is given, stop all instances of SMACKBench
    if (args.mode == 'stop'):
        #Since only one instance of benchexec can run at a given time,
        #we can blindly kill all running SMACKBench.py instances
        subprocess.check_call(['pkill','-SIGTERM','-f','SMACKBench.py'])
    #Read the config file
    cfgObj = get_config(args.config_file)
    #EVERYTHING in SMACKBench is relative to dataFolder (internally, that is)
    #  however, this must be adjusted within this program. (Except for config
    #  file location)
    #  Externally, (in config file, for example), paths are relative to root
    #As a result, all paths that come as input to this program get adjusted
    #  from being relative to root to being relative to dataFolder before
    #  being used
    os.chdir(cfgObj['dataFolder'])
    #Make sure folders are created
    for fold in [cfgObj['runsFolder'], cfgObj['logFolder']]:
        try:
            os.mkdir(fold)
        except OSError:
            #Already exists
            pass
    #If server command given
    if(args.mode == 'server'):
        #Determine the destination log file
        logFile = path.join(cfgObj['logFolder'], gethostname() + '.log')
        #Start the run_server function as a daemon, redirecting stderr to
        #stdout, and stdout to the log file
        print("To see benchexec console outputin real time, run 'tail -f {0}'".format(path.join(cfgObj['dataFolder'],logFile)))
        with daemon.DaemonContext(working_directory = os.getcwd(),
                                  stderr=sys.stdout,
                                  stdout=open(logFile, 'a')):
            run_server(cfgObj, path.join('..', args.queue_file),
                       args.concurrentRuns, args.memoryPerRun, args.description)
        
    else:
        #if here, we're in run mode
        #signal.signal(signal.SIGTERM, handle_sigterm)
        runSMACKBench(cfgObj, args.svcomp_set, args.inputXmlFile,
                      args.concurrentRuns, args.memoryPerRun,
                      args.description)
