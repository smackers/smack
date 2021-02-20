#! /usr/bin/env python3

import xml.etree as etree
import xml.etree.ElementTree as ET
from xml.etree.ElementTree import ElementTree
import xml.dom.minidom as minidom
import json
import re
import sys
import pprint
import os
import hashlib
import datetime

nextNum = 0

def prettify(elem):
    """Return a pretty-printed XML string for the Element.
    """
    rough_string = ET.tostring(elem, 'utf-8')
    reparsed = minidom.parseString(rough_string)
    return reparsed.toprettyxml(indent="    ", encoding='UTF-8')

def addKeyDefs(root):
    """Each graphml must define the keys that are available in the nodes containing data.
       These are defined in <key> nodes.  This function builds a table containing the keys
       that need to be defined for the svcomp witness format, and then adds them to the
       xml root passed in as the parameter"""
    keys = []
    #keys are [attr.name, attr.type, for, id, hasDefault, defaultVal]
    keys.append(["assumption",         "string",  "edge",  "assumption",     False])
    keys.append(["assumption.scope",         "string",  "edge",  "assumption.scope",     False])
    keys.append(["assumption.resultfunction",         "string",  "edge",  "assumption.resultfunction",     False])
    keys.append(["sourcecode",         "string",  "edge",  "sourcecode",     False])
    keys.append(["witness-type", "string",  "graph", "witness-type", False])
    keys.append(["sourcecodeLanguage", "string",  "graph", "sourcecodelang", False])
    keys.append(["producer", "string",  "graph", "producer", False])
    keys.append(["specification", "string",  "graph", "specification", False])
    keys.append(["programfile", "string",  "graph", "programfile", False])
    keys.append(["programhash", "string",  "graph", "programhash", False])
    keys.append(["architecture", "string",  "graph", "architecture", False])
    keys.append(["creationtime", "string",  "graph", "creationtime", False])
    keys.append(["tokenSet",           "string",  "edge",  "tokens",         False])
    keys.append(["originTokenSet",     "string",  "edge",  "origintokens",   False])
    keys.append(["negativeCase",       "string",  "edge",  "negated",        True, "false"])
    #keys.append(["lineNumberInOrigin", "int",     "edge",  "originline",     False])
    keys.append(["startline", "int",     "edge",  "startline",     False])
    keys.append(["originFileName",     "string",  "edge",  "originfile",     False]) # example has default
    keys.append(["nodeType",           "string",  "node",  "nodetype",       True, "path"])
    keys.append(["isFrontierNode",     "boolean", "node",  "frontier",       True, "false"])
    keys.append(["isViolationNode",    "boolean", "node",  "violation",      True, "false"])
    keys.append(["isEntryNode",        "boolean", "node",  "entry",          True, "false"])
    keys.append(["isSinkNode",         "boolean", "node",  "sink",           True, "false"])
    keys.append(["enterFunction",      "string",  "edge",  "enterFunction",  False])
    keys.append(["returnFromFunction", "string",  "edge",  "returnFrom",     False])
    for key in keys:
        xmlKey = ET.SubElement(root, 'key')
        xmlKey.set("attr.name", key[0])
        xmlKey.set("attr.type", key[1])
        xmlKey.set("for",       key[2])
        xmlKey.set("id",        key[3])
        if(key[4]):
            default = ET.SubElement(xmlKey, 'default')
            default.text = key[5]

def addKey(element, keyType, text):
    """This function adds a <data> element of which is a key of  type 'keyType',
       where the <data>'s value is 'text'.  The <data> element is added as a 
       child of 'element'"""
    newKey = ET.SubElement(element, "data", attrib={"key":keyType})
    newKey.text = text

def addGraphNode(tree, data={}):
    """Adds a node to the xml 'tree' , as a child of the main <graph> element.
       Nodes get a serially incrementing ID, prefaced with "A".
       For each item in the data input parameter, a <data> element is created
       as a child to the new <node> element"""
    global nextNum
    #Get graph element
    graph = tree.find('graph')
    ID = "A"+str(nextNum)
    newNode = ET.SubElement(graph, "node", attrib={"id":ID})
    nextNum += 1
    for datum in data:
        addKey(newNode, datum, data[datum])
    #Returing ID so caller can save ID for reference in edge
    return ID
    #return newNode

def addGraphEdge(tree, source, target, data={}):
    """Adds an <edge> element to the main <graph> element.  The 'source' and 'target'
       are added as attributes to the new <edge> element, and <data> nodes are added
       for each item in 'data'.
       'source' and 'target' should refer to valid <node> elements which are children
       to the main <graph> element"""
    graph = tree.find('graph')
    newEdge = ET.SubElement(graph, "edge", attrib={"source":source,"target":target})
    for datum in data:
        addKey(newEdge, datum, data[datum])
    return newEdge
        

def buildEmptyXmlGraph(args, hasBug):
    """Builds an empty witness xml file, with all the keys we will be using 
       already defined."""
    root = ET.Element('graphml')
    root.set("xmlns:xsi","http://www.w3.org/2001/XMLSchema-instance")
    root.set("xmlns", "http://graphml.graphdrawing.org/xmlns")
    tree = ElementTree(root)
    addKeyDefs(root)
    graph = ET.SubElement(root, "graph", attrib={"edgedefault" : "directed"})

    addKey(graph, "witness-type", "violation_witness" if hasBug else "correctness_witness")
    addKey(graph, "sourcecodelang", "C")
    from smack.top import VERSION
    addKey(graph, "producer", "SMACK " + VERSION)
    with open(args.svcomp_property, 'r') as ppf:
      addKey(graph, "specification", ppf.read().strip())
    programfile = os.path.abspath(args.orig_files[0])
    addKey(graph, "programfile", programfile)
    with open(programfile, 'r') as pgf:
      addKey(graph, "programhash", hashlib.sha256(pgf.read().encode('utf-8')).hexdigest())
    addKey(graph, "architecture",
            re.search(r'-m(32|64)', args.clang_options).group(1) + 'bit')
    addKey(graph, "creationtime", datetime.datetime.now().replace(microsecond=0).isoformat())
    return tree

def formatAssign(assignStmt):
    if not assignStmt:
      return assignStmt
    m = re.match(r'(.*)=(.*)', assignStmt)
    if m:
      repl = lambda x: '='+ x.group(1) + 'U' if x.group(2) is not None else ''
      return re.sub(r'=(\s*\d+)(bv\d+)', repl, m.group(1) + "==" + m.group(2))
    else:
      return ""

def isSMACKInitFunc(funcName):
  return funcName == '$initialize' or funcName == '__SMACK_static_init' or funcName == '__SMACK_init_func_memory_model'

def smackJsonToXmlGraph(strJsonOutput, args, hasBug, status):
    """Converts output from SMACK (in the smackd json format) to a graphml
       format that conforms to the SVCOMP witness file format"""
    # Build tree & start node
    tree = buildEmptyXmlGraph(args, hasBug)
    # Add the start node, which gets marked as being the entry node
    start = addGraphNode(tree, {"entry":"true"})
    if hasBug and not args.pthread:
      # Convert json string to json object
      smackJson = json.loads(strJsonOutput)
      # Get the failure node, and the list of trace entries to get there
      jsonViolation = smackJson["failsAt"]
      jsonTraces = smackJson["traces"]

      lastNode = start
      lastEdge = None
      pat = re.compile(".*/smack/lib/.+\.[c|h]$")
      prevLineNo = -1
      prevColNo = -1
      callStack = [('main', '0')]
      # Loop through each trace
      for jsonTrace in jsonTraces:
        # Make sure it isn't a smack header file
        if "ASSERTION FAILS" in jsonTrace["description"]:
          newNode = addGraphNode(tree)
          # addGraphNode returns a string, so we had to search the graph to get the node that we want
          vNodes =tree.find("graph").findall("node")
          for vNode in vNodes:
            if vNode.attrib["id"] == newNode:
              addKey(vNode, "violation", "true")
          attribs = {"startline":str(jsonViolation['line'])}
          addGraphEdge(tree, lastNode, newNode, attribs)
          break
        if not pat.match(jsonTrace["file"]):
          desc = jsonTrace["description"]
          formattedAssign = formatAssign(desc)
          # Make sure it is not return value
          if formattedAssign and formattedAssign.startswith('smack:ext:__VERIFIER_nondet'):
            tokens = formattedAssign.split('==')
            nondet_func = tokens[0].strip()[len('smack:ext:'):]
            val = tokens[1].strip()
            new_assumption = '\\result == %s;' % val
          # Create new node and edge
            newNode = addGraphNode(tree)
            attribs = {"startline":str(jsonTrace["line"])}
            attribs["assumption"] = new_assumption
            attribs['assumption.resultfunction'] = nondet_func
            scope_func = callStack[-1][0]
            attribs["assumption.scope"] = scope_func.split('.')[0] if '.' in scope_func else scope_func
            newEdge = addGraphEdge(tree, lastNode, newNode, attribs)
            prevLineNo = jsonTrace["line"]
            prevColNo = jsonTrace["column"]
            lastNode = newNode
            lastEdge = newEdge
          if "CALL" in desc:
            # Add function to call stack
            calledFunc = str(jsonTrace["description"][len("CALL "):]).strip()
            if calledFunc.startswith("devirtbounce"):
              print("Warning: calling function pointer dispatch procedure at line {0}".format(jsonTrace["line"]))
              continue
            if isSMACKInitFunc(calledFunc):
              continue
            callStack.append((calledFunc, jsonTrace["line"]))
          if "RETURN from" in desc:
            returnedFunc = str(desc[len("RETURN from "):]).strip()
            if returnedFunc.startswith("devirtbounce"):
              print("Warning: returning from function pointer dispatch procedure at line {0}".format(jsonTrace["line"]))
              continue
            if isSMACKInitFunc(returnedFunc):
              continue
            if returnedFunc != callStack[-1][0]:
              raise RuntimeError('Procedure Call/Return dismatch at line {0}. Call stack head: {1}, returning from: {2}'.format(jsonTrace["line"], callStack[-1][0], returnedFunc))
            callStack.pop()
    print()
    print()
    return prettify(tree.getroot())


if __name__ == '__main__':
    jsonStr = """{"passed?": false, "verifier": "corral", "traces": [{"column": 5, "line": 3, "description": "", "file": "fail.c", "threadid": 1}, {"column": 5, "line": 4, "description": "", "file": "fail.c", "threadid": 1}, {"column": 5, "line": 5, "description": "", "file": "fail.c", "threadid": 1}, {"column": 12, "line": 5, "description": "", "file": "fail.c", "threadid": 1}, {"column": 21, "line": 5, "description": "", "file": "fail.c", "threadid": 1}, {"column": 21, "line": 5, "description": "CALL __SMACK_assert", "file": "fail.c", "threadid": 1}, {"column": 26, "line": 40, "description": "", "file": "/home/mcarter/projects/smack-project/smack/install/include/smack/smack.h", "threadid": 1}, {"column": 3, "line": 41, "description": "", "file": "/home/mcarter/projects/smack-project/smack/install/include/smack/smack.h", "threadid": 1}, {"column": 3, "line": 41, "description": "ASSERTION FAILS", "file": "/home/mcarter/projects/smack-project/smack/install/include/smack/smack.h", "threadid": 1}, {"column": 21, "line": 5, "description": "RETURN from __SMACK_assert ", "file": "fail.c", "threadid": 1}, {"column": 21, "line": 5, "description": "Done", "file": "fail.c", "threadid": 1}], "threadCount": 1, "failsAt": {"column": 1, "line": 41, "description": "error PF5001: This assertion can fail", "file": "/home/mcarter/projects/smack-project/smack/install/include/smack/smack.h"}}"""
    if len(sys.argv) > 1:
       jsonStr = open(sys.argv[1], "r").read()

    print((smackJsonToXmlGraph(jsonStr)))


'''print(prettify(tree.getroot()))
tree.write("test.xml",
           encoding='UTF-8',
           xml_declaration=True)
'''

"""Example graphml witness file:

<?xml version="1.0" encoding="UTF-8" standalone="no"?>
<graphml xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance" xmlns="http://graphml.graphdrawing.org/xmlns">
  <key attr.name="assumption" attr.type="string" for="edge" id="assumption"/>
  <key attr.name="sourcecode" attr.type="string" for="edge" id="sourcecode"/>
  <key attr.name="sourcecodeLanguage" attr.type="string" for="graph" id="sourcecodelang"/>
  <key attr.name="tokenSet" attr.type="string" for="edge" id="tokens"/>
  <key attr.name="originTokenSet" attr.type="string" for="edge" id="origintokens"/>
  <key attr.name="negativeCase" attr.type="string" for="edge" id="negated">
    <default>false</default>
  </key>
  <key attr.name="lineNumberInOrigin" attr.type="int" for="edge" id="originline"/>
  <key attr.name="originFileName" attr.type="string" for="edge" id="originfile">
    <default>&lt;none&gt;</default>
  </key>
  <key attr.name="nodeType" attr.type="string" for="node" id="nodetype">
    <default>path</default>
  </key>
  <key attr.name="isFrontierNode" attr.type="boolean" for="node" id="frontier">
    <default>false</default>
  </key>
  <key attr.name="isViolationNode" attr.type="boolean" for="node" id="violation">
    <default>false</default>
  </key>
  <key attr.name="isEntryNode" attr.type="boolean" for="node" id="entry">
    <default>false</default>
  </key>
  <key attr.name="isSinkNode" attr.type="boolean" for="node" id="sink">
    <default>false</default>
  </key>
  <key attr.name="enterFunction" attr.type="string" for="edge" id="enterFunction"/>
  <key attr.name="returnFromFunction" attr.type="string" for="edge" id="returnFrom"/>
  <graph edgedefault="directed">
    <data key="sourcecodelang">C</data>
    <node id="A0">
      <data key="entry">true</data>
    </node>
    <node id="A1"/>
    <edge source="A0" target="A1">
      <data key="tokens">758</data>
      <data key="originline">758</data>
      <data key="originfile">../data/sv-benchmarks/ssh-simplified/s3_clnt_1_false-unreach-call.cil.c</data>
      <data key="sourcecode">int s ;</data>
    </edge>
    <node id="A1">
      <data key="violation">true</data>
    </node>
  </graph>
</graphml>
"""
