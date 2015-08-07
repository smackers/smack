#!/usr/bin/python

from __future__ import print_function
import re
sys.dont_write_bytecode = True # prevent creation of .pyc files

###
### This file contains functions for converting parameters as passed by 
### ParamILS into the form they need to be for the destination tool.
###

#Creates list of Param objects from extraArgs
def parseParams(extraArgs):
    params = list()
    for i in range(len(extraArgs), 2):
        nameStr,valueStr = extraArgs[i], extraArgs[i+1]
        arg = re.match(r'-(SMACK|CORRAL|BOOGIE|Z3)__(isFlag__)(.*)', nameStr)
        isFlag = True if arg.group(2) else False
        params += Param(arg.group(1), arg.group(3), valueStr, isFlag)
    return params

#Wraps a Z3 option as a Corral/Boogie Option (e.g., a.b=10 -> /z3opt:a.b=10)
def wrapZ3param(tool, z3param):
    if tool in ['CORRAL', 'BOOGIE']:
        if z3param.tool=='Z3':
            #z3 parameters should always be a single item
            return Param(tool, 'z3opt', z3param.asStringList()[0], False)
        else:
            msg = "Wrapped Z3 params must be Z3 params, not {0} params"
            raise msg.format(z3param.tool)
    else:
        msg = "Unsupported tool for wrapping Z3 param: {0}"
        raise msg.format(tool)

#Filters list of params to include only requested type
def filterParams(tool, params):
    return [p for p in params if p.tool == tool]

def param2cmdArgList(params):
    #Flatten the multi item SMACK params...
    return [argStr for param in params for argStr in param.asStringList()]
    

class Param:
        
    def __init__(self, tool, name, value, isFlag):
        self.tool = tool
        self.name = name
        self.value = value
        self.isFlag = isFlag
        if tool in ['CORRAL', 'BOOGIE']:
            self.prefix = '/'
            self.delim = ':'
        elif tool == 'Z3':
            self.prefix = ''
            self.delim = '='
        elif tool == 'SMACK':
            self.prefix = '-'
            self.delim = ''
        else:
            raise "Unsupported Tool: {0}".format(tool)
                                    
    def __eq__(self, other):
        return (self.tool   == other.tool  and
                self.name   == other.name  and
                self.value  == other.value and
                self.isFlag == other.isFlag)

    # Always returns a list of strings (to append to existing list)
    def asStringList(self):
        if self.isFlag:
            allowedFlagTrue =  ['True','true','t','yes','1']
            allowedFlagFalse = ['False','false','f','no','0']
            if self.value in allowedFlagTrue:
                return self.prefix + self.name
            elif self.value in allowedFlagFalse:
                return list()
            else:
                msg = "Flags parameters must be one of the following: {0}"
                raise msg.format(",".join(allowedFlagTrue) + "," + 
                                 ",".join(allowedFlagFalse))
        else:
            if self.delim == '':
                return [self.prefix + self.name, self.value]
            else:
                return [self.prefix + self.name + self.delim + self.value]
