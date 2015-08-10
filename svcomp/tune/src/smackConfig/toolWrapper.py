#!/usr/bin/python

from __future__ import print_function
import sys
import time
import subprocess
import traceback
sys.dont_write_bytecode = True # prevent creation of .pyc files

#Args Passed by ParamILS:
#    0 - script name
#    1 - instance name (input full filename)
#    2 - instance specific information
#        (this is the <rest> from instance file
#        (all columns after filename))
#    3 - cutoff time (time limit)
#    4 - cutoff length (??? - pass "-1" if this param doesn't make sense)
#    5 - seed (??? probably doesn't apply to SMACK
#        (maybe z3 can take seed?))
#   6+ - All remaining params are the parameters being tried by paramils


### A base class to derive tool wrappers for ParamILS
### The main purpose of classing this is to separate the
### logic needed to prepare a tools input/output for use
### with paramILS.  The derived classes should be short,
### and only need to deal with logic related to that tool.
class ToolRun:

    ### Takes argv array passed during paramils call to tool
    ### Parses these arguments, creating a "ToolRun" for the tool
    ###
    def __init__(self, toolArgs):
        self.inputFile    = toolArgs[1]
        self.rest         = toolArgs[2]
        self.cutoffTime   = int(float(toolArgs[3]))
        self.cutoffLength = int(float(toolArgs[4]))
        self.seed         = int(float(toolArgs[5]))
        self.rawArgs      = toolArgs[6:]
        self.preparedArgs = self.prepareCmd(self.inputFile, self.rest,
                                            self.cutoffTime,self.cutoffLength,
                                            self.seed, self.rawArgs)

    ### Child class must define
    ### Prepares cmd arglist for python's subprocess module
    ### 
    ### Takes input args
    ### Returns an cmd arg list (including cmd) to be passed to python's
    ### subprocess module
    def prepareCmd(self, inputFile, rest, cutoffTime, cutoffLength, seed,
                    rawArgs):
        raise NotImplementedError("Must Implement This Method")
    
    ### Child class must define
    ### Parses the output returned from the tool
    ### Must return "CORRECT", "WRONG", or "TIMEOUT"
    def parseOutput(self, inputFile, output):
        raise NotImplementedError("Must Implement This Method")
    
    ### Calls the child class's implementation of executeRun(),
    ### and times the execution.
    ### Then calls child class's parseOutput()
    ###
    ### Takes an input file name, a time limit, and the arguments
    ### Returns a list of six items, 
    def executeRun(self):
        startTime = time.time()
        p = subprocess.Popen(self.preparedArgs,
                             stdout=subprocess.PIPE, 
                             stderr=subprocess.PIPE)
        out, err  = p.communicate()
        endTime = time.time()
        self.output = (out+err).decode('utf-8')
        self.runtime = endTime - startTime
        try:
            self.outcome = self.parseOutput(self.inputFile, self.output)
        except AttributeError as e:
            print("###" + self.output + "###", file=sys.stderr)
            traceback.print_exc()
            exit()
        self.runlength = -1
        self.best_sol  = -1
        self.seed      = -1

    ### Prints result string to console expected by ParamILS
    def printResults(self):
        #Print paramils result string
        msg  = "Result for ParamILS: %(self.outcome)s, "
        msg += "%(self.runtime)f, %(self.runlength)d, %(self.best_sol)d, "
        msg += "%(seed)d"
        print(msg % locals())
        #Print smack output
        print(self.output)
