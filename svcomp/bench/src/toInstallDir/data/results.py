#!/usr/bin/env python3
import cgitb
import cgi
import datetime
import subprocess
import sys
import os
cgitb.enable()

from lib import *
sys.dont_write_bytecode = True # prevent creation of .pyc files


runRoot = "."
runFolderPrefix = "exec"
tblGenExe = "../benchexec/bin/table-generator"
scratchDir = "."

def printError(msg):
    print("<h1>Bad results.py query</h1><hr/>")
    print("<p>Query failed with the following message:</p>")
    print("<p>" + msg + "</p>")
    exit()

def filterResultsByCategory(runSets, form):
    ret = []
    for runset in runSets:
        if runset.fileSet == form['category'].value:
            ret.append(runset)
    return ret

def filterResultsByOptions(runSets, form, allOptions):
    badOpts = dict()
    #If the option was passed, we'll build a set of negative options, 
    # based on set difference between allOptions and form passed options
    for opt in allOptions.keys():
        if opt in form:
            #detect whether single value was passed, or a list
            if isinstance(form.getvalue(opt), list):
                badOpts[opt] = set(allOptions[opt]) - set(form.getvalue(opt))
            else:
                badOpts[opt] = set(allOptions[opt]) - set([form[opt].value])
    #Only keep set if it doesn't have any badopts
    ret = []
    for runset in runSets:
        keep = True
        for opt in badOpts.keys():
            #If option exists for run, and it is in bad list, unkeep it
            if opt in runset.options and runset.options[opt] in badOpts[opt]:
                keep = False
        if keep:
            ret.append(runset)
    return ret

def generateTable(runSets):
    #Get list of output xml files
    xmlFiles = []
    for runset in runSets:
        xmlFiles.append(runset.outXml)
    filenameBase = "results"
    
    cmd = [tblGenExe, "-o", scratchDir, "-n", filenameBase, "--printHTML", "--no-diff"] + xmlFiles
    try:
        out = subprocess.check_output(cmd, stderr=subprocess.STDOUT)
        print(out.decode('utf-8'))
    except subprocess.CalledProcessError as e:
        out = e.output
        printError("table-generator failed with the following output:\n<pre>" + out.decode('utf-8') + "</pre>")


if __name__ == '__main__':
    print("Content-Type: text/html")    # HTML is following
    print()                             # blank line, end of headers
    print("something")
    form = cgi.FieldStorage()

    runSets = getAllRunSets(runRoot, runFolderPrefix)
    allOptions = getAllOptionsUsed(runSets)

    if not "category" in form:
        printError("No category parameter passed")
    runSets = filterResultsByCategory(runSets, form)
    runSets = filterResultsByOptions(runSets, form, allOptions)
    generateTable(runSets)
