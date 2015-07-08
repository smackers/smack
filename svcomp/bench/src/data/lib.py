import cgi 
import glob
import xml.etree.ElementTree as ET
from os import path
import sys
import re
sys.dont_write_bytecode = True # prevent creation of .pyc files

"""
This file provides some utility functions that are used by both index.py and
results.py.

It provides functionality mainly for understanding BenchExec's xml input and
output formats.
"""

def natural_sort_key(s, _nsre=re.compile('([0-9]+)')):
    """
    A sorting function for sorting possible option values as integers rather than
    lexigraphically.
    """
    return [int(text) if text.isdigit() else text.lower()
            for text in re.split(_nsre, s)]

class RunSet:
    """
    A class that represents a BenchExec run set.  It contains information 
    critical to filtering, selecting, and displaying run sets
    """
    def __init__(self, outputXml, inputXml):
        """
        Creates a RunSet based on a run's input and output xml files
        """
        self.inXml = inputXml
        self.outXml = outputXml
        self.name = ET.parse(self.outXml).getroot().get("name")
        self.options = self.getOptions()
        self.fileSet = self.getSetName()

    def getOptions(self):
        """
        Gets the command line options used when calling SMACK for this run set.
        """
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
        """
        Gets the svcomp category (or 'Set' name) defining the specific benchmarks
        that were executed.
        """
        #sourcefile Set name is found as last token before .xml in output filename
        #Remove file extension
        noExt = path.splitext(self.outXml)[0]
        return noExt.split(".")[-1]

def getAllRunSets(searchRoot, folderPrefix):
    """
    Finds all xml files matching the path searchRoot/folderPrefix*/results/*.xml

    Currently, this is set to only find run sets that have already been witness.
    This should probably be reconsidered (perhaps a filter option in index.py
    that allows users to select all run sets, or only those that have been
    witness checked?)
    """
    allOutXml = glob.glob(searchRoot + "/" + folderPrefix + "*/results/*witchecked.*.xml")
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
    """
    Returns a list of svcomp categories (or "Sets") for which result sets exist.

    This is used to populate the "Category" drop down in index.py.
    """
    usedSets = set()
    for runset in runSets:
        usedSets.add(runset.fileSet)
    return sorted(list(usedSets))


def getAllOptionsUsed(runSets):
    """
    Returns a list of all options and corresponding values in use in the input
    set of result sets.

    This is used by index.py to populate the possible options that can be used to
    filter result sets.
    """
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


