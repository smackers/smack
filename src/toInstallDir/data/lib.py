import glob
import xml.etree.ElementTree as ET
from os import path
import sys
sys.dont_write_bytecode = True # prevent creation of .pyc files

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


