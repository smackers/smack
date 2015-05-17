#!/usr/bin/env python3
import cgitb
import cgi
import glob
import xml.etree.ElementTree as ET
from os import path
cgitb.enable()

runRoot = "."
runFolderPrefix = "exec"

class RunSet:
    def __init__(self, outputXml, inputXml):
        self.inXml = inputXml
        self.outXml = outputXml
        self.name = ET.parse(self.outXml).getroot().get("name")
        self.options = self.getOptions()
        self.fileSet = self.getSetName()

    def getOptions(self):
        inRoot = ET.parse(self.inXml).getroot()
        #Find rundefinition node with matching name, and get its option children
        rundefOptions = inRoot.findall('rundefinition[@name="' + self.name + '"]/option')
        options = dict()
        for opt in rundefOptions:
            options[opt.get("name")] =  opt.text
        return options

    def getSetName(self):
        #sourcefile Set name is found as last token before .xml in output filename
        #Remove file extension
        noExt = path.splitext(self.outXml)[0]
        #Use rundefinition name  plus "." as delimiter
        return noExt.split(self.name + ".")[1]

#Finds all xml files matching the path searchRoot/folderPrefix*/results/*.xml
def getAllRunSets(searchRoot, folderPrefix):
    allOutXml = glob.glob(searchRoot + "/" + folderPrefix + "*/results/*.xml")
    runSets = []
    for outFile in allOutXml:
        inputFilename = ET.parse(outFile).getroot().get("benchmarkname") + ".xml"
        #Get rid of outFile name and results folder
        inputPath = path.split(path.split(outFile)[0])[0]
        inFile = path.join(inputPath,inputFilename)
        runSets.append(RunSet(outFile,inFile))
        
    return runSets

def getSourcefileSetsUsed(runSets):
    usedSets = set()
    for runset in runSets:
        usedSets.add(runset.fileSet)
    return sorted(list(usedSets))


def getAllOptionsUsed(runSets):
    possibleOptions = dict()
    for runset in runSets:
        for opt in runset.options:
            if opt in possibleOptions:
                possibleOptions[opt].add(runset.options[opt])
            else:
                possibleOptions[opt] = set([runset.options[opt]])
    #Convert from set to list and sort
    for opt in possibleOptions:
        possibleOptions[opt] = sorted(possibleOptions[opt])
    return possibleOptions


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
<form method="post" action="index.py">''')

    usedFilesets = getSourcefileSetsUsed(runSets)
    print('''
    <table>
    <tr><td>Category:</td><td><select name="filesets">''')

    for fileset in usedFilesets:
        print('''
        <option value="{0}">{0}</option>'''.format(fileset))
    print('''
    </select></td></tr>''')

    for key in optionKeys:
        print('''
        <tr><td>{0}:</td>'''.format(key))
        for val in options[key]:
            print('''
        <td><input type="checkbox" name="--unroll" value="{0}" /> {0}</td>'''.format(val))
        print('''
        </tr>''')

    print('''
    <tr><td><input type="submit" value="Submit" name="Submit"></td>
        <td><input type="submit" value="Clear" name="Clear"></td></tr>
    </table>''')
    print('''
</form>''')

    if "Submit" in form:
        print("Submitting form")
