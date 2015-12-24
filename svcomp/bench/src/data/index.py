#!/usr/bin/env python
from lib import *
import sys
import cgitb
import cgi
cgitb.enable()
sys.dont_write_bytecode = True # prevent creation of .pyc files

"""
This file is the landing web page for a SMACKBench instance.  It provides an
interface for selecting which benchmark results to display.  It allows users to
filter svcomp benchmark sets based on set name and command line options used when
executing SMACK.

Upon form submission, results.py is called, with filter details passed as cgi 
parameters.  results.py is responsible for finding matching result sets and 
generating a table containing these result sets.
"""


runRoot = "."
runFolderPrefix = "exec"
if __name__ == '__main__':
    print "Content-Type: text/html"     # HTML is following
    print                               # blank line, end of headers
    form = cgi.FieldStorage()

    runSets = getAllRunSets(runRoot, runFolderPrefix)
    options = getAllOptionsUsed(runSets)
    optionKeys = sorted(options.keys())
    for runset in runSets:
        if 'witcheck' in runset.outXml:
            runSets.remove(runset)
    runSets.sort(key=lambda x: x.inXml, reverse=True)
    print '''
<h1>SMACK+CORRAL Benchmark Results</h1><hr/>
<p>Select a set, and select the command line options to include</p>
<p>Any option with no selected values will include all values for that option</p><hr/>
<form method="get" action="results.py">'''

    usedFilesets = getSourcefileSetsUsed(runSets)
    print '''
    <table>
    <tr><td>Category:</td><td><select name="category">'''

    for fileset in usedFilesets:
        print '''
        <option value="{0}">{0}</option>'''.format(fileset)
    print '''
    </select></td></tr>'''

    for key in optionKeys:
        print '''
        <tr><td>{0}:</td><td>'''.format(key)
        for val in options[key]:
            print '''
        <input type="checkbox" name="{0}" value="{1}" /> {1}'''.format(key, val)
        print '''
        </td></tr>'''

    print '''
    <tr><td align="center" colspan="2" valign="middle">
          <input type="submit" value="Submit" name="Submit"></form>
    </td></tr>
    <tr><td align="center" colspan="2" valign="middle">
          <form method="post" action="index.py">
            <input type="submit" value="Clear" name="Clear">
          </form>
    </td></tr>
    </table>
    <hr/>
    Or select a specific set to view (ignores filters above):<br/><br/>
    <form method="get" action="results.py">
    RunSet:<select name="runset">'''

    for runset in runSets:
        print '''
        <option value="{0}">{0}</option>'''.format(runset.runsetFolder)
    print '''
    </select>      
      <br/><input type="submit" value="Submit" name=Submit">
    </form>
    '''
