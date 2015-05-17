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

    def getOptions(self):
        inRoot = ET.parse(self.inXml).getroot()
        #Find rundefinition node with matching name, and get its option children
        rundefOptions = inRoot.findall('rundefinition[@name="' + self.name + '"]/option')
        options = dict()
        for opt in rundefOptions:
            options[opt.get("name")] =  opt.text
        return options

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

def printOptions(options):
    optionKeys = sorted(options.keys())

    print('''
<form method="post" action="index.py">''')
    for key in optionKeys:
        print('''
    <p>
        {0}: '''.format(key))
        for val in options[key]:
            print('''
        <input type="checkbox" name="--unroll" value="{0}" /> {0}'''.format(val))

        print('''
    </p>''')
    print('''
</form>''')



    

if __name__ == '__main__':
    print("Content-Type: text/html")    # HTML is following
    print()                             # blank line, end of headers

    
    runSets = getAllRunSets(runRoot, runFolderPrefix)
    usedOptions = getAllOptionsUsed(runSets)
    printOptions(usedOptions)

