#!/usr/bin/env python
from lib import *
import datetime
import subprocess
import sys
import os
import cgitb
import cgi
cgitb.enable()
sys.dont_write_bytecode = True # prevent creation of .pyc files

"""
This file generates a BenchExec table that includes the BenchExec result sets
that are selected by the filter constraints which are passed in as cgi parameters
to this script.

It calls BenchExec's 'tablegenerator' on output xml files matching the filter
parameters.  The html output from 'tablegenerator' is sent to stdout, which=
causes the dynamically generated webpage to be displayed at the client's browser.
"""


runRoot = "."
runFolderPrefix = "exec"
tblGenExe = "../benchexec/bin/table-generator"
scratchDir = "."

def printError(msg):
    """
    Outputs python stack trace as html, for ease of readability in client's web
    browser.
    """
    print "<h1>Bad results.py query</h1><hr/>"
    print "<p>Query failed with the following message:</p>"
    print "<p>" + msg + "</p>"
    exit()

def filterResultsByCategory(runSets, form):
    """
    Filters out result sets that don't match the svcomp category (set) given in
    the cgi form input parameters.
    """
    ret = []
    for runset in runSets:
        if runset.fileSet == form['category'].value:
            ret.append(runset)
    return ret

def filterResultsByOptions(runSets, form, allOptions):
    """
    Filters out result sets that don't match the command line options selected
    by the form input parameters.

    For options with no value selected (e.g., none of the --unroll checkboxes 
    were checked), result sets will not be filtered based on this option (in
    other words, it doesn't make sense to return an empty table).

    For options with at least one value selected, only result sets using that 
    option (with one of the selected values) are included.  (This means that
    if --unroll 2 and --unroll 4 were checked, result sets that don't specify the
    --unroll option are excluded).

    For boolean flags, the 'False' checkbox will include only result sets 
    generated without the flag being used.  When the 'True' checkbox is set,
    only result sets generated with the flag specified are included.
    """
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
    """
    Calls BenchExec's 'tablegenerator' with the selected run set xml files as
    arguments.

    'tablegenerator' output is sent to stdout, which is sent to the remote client
    by apache.
    """
    #Get list of output xml files
    xmlFiles = []
    for runset in runSets:
        xmlFiles.append(runset.outXml)
    filenameBase = "results"
    
    cmd = [tblGenExe, "-o", "-", "-f", "html", "-q", "--no-diff"] + xmlFiles
    try:
        out = subprocess.check_output(cmd, stderr=subprocess.STDOUT)
        print out.decode('utf-8')
    except subprocess.CalledProcessError as e:
        out = e.output
        printError("table-generator failed with the following output:\n<pre>" + out.decode('utf-8') + "</pre>")


if __name__ == '__main__':
    print "Content-Type: text/html"    # HTML is following
    print                              # blank line, end of headers
    form = cgi.FieldStorage()

    runSets = getAllRunSets(runRoot, runFolderPrefix)
    allOptions = getAllOptionsUsed(runSets)

    if not "category" in form:
        printError("No category parameter passed")
    runSets = filterResultsByCategory(runSets, form)
    runSets = filterResultsByOptions(runSets, form, allOptions)
    runSets.sort(key=lambda x: x.inXml)
    generateTable(runSets)
