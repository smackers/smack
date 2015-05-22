#!/usr/bin/env python3
import cgitb
import cgi
cgitb.enable()

from lib import *

runRoot = "."
runFolderPrefix = "exec"
if __name__ == '__main__':
    print("Content-Type: text/html")    # HTML is following
    print()                             # blank line, end of headers
    form = cgi.FieldStorage()

    runSets = getAllRunSets(runRoot, runFolderPrefix)
    options = getAllOptionsUsed(runSets)
    optionKeys = sorted(options.keys())
    print('''
<h1>SMACK+CORRAL Benchmark Results</h1><hr/>
<p>Select a set, and select the command line options to include</p>
<p>Any option with no selected values will include all values for that option</p><hr/>
<form method="get" action="results.py">''')

    usedFilesets = getSourcefileSetsUsed(runSets)
    print('''
    <table>
    <tr><td>Category:</td><td><select name="category">''')

    for fileset in usedFilesets:
        print('''
        <option value="{0}">{0}</option>'''.format(fileset))
    print('''
    </select></td></tr>''')

    for key in optionKeys:
        print('''
        <tr><td>{0}:</td><td>'''.format(key))
        for val in options[key]:
            print('''
        <input type="checkbox" name="{0}" value="{1}" /> {1}'''.format(key, val))
        print('''
        </td></tr>''')

    print('''
    <tr><td align="center" colspan="2" valign="middle">
          <input type="submit" value="Submit" name="Submit"></form>
    </td></tr>
    <tr><td align="center" colspan="2" valign="middle">
          <form method="post" action="index.py">
            <input type="submit" value="Clear" name="Clear">
          </form>
    </td></tr>
    </table>''')
