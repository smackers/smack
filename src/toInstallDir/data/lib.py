import cgi 
import glob
import xml.etree.ElementTree as ET
from os import path
import sys
sys.dont_write_bytecode = True # prevent creation of .pyc files
import re

def natural_sort_key(s, _nsre=re.compile('([0-9]+)')):
    return [int(text) if text.isdigit() else text.lower()
            for text in re.split(_nsre, s)]

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
            if options[opt.get("name")] == None:
                options[opt.get("name")] = "True"
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
        
    #For each set, if an option isn't used, set it to false.
    allOpts = getAllOptionsUsed(runSets)
    for runset in runSets:
        for opt in allOpts:
            if opt not in runset.options:
                runset.options[opt] = "False"
        
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
        #Add True/False for flag options
        if possibleOptions[opt] == {None}:
            possibleOptions[opt] = ["True", "False"]
        else:
            possibleOptions[opt] = sorted(possibleOptions[opt], key=natural_sort_key)
    return possibleOptions


