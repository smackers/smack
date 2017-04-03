import os
import re

import logging
import xml.etree.ElementTree as ET

import benchexec.util as util
import benchexec.tools.template
import benchexec.result as result

"""
This file defines Smack for BenchExec.  It defines a class that inherits from
BenchExec's BaseTool class, which declares functions that the BenchExec framework
uses to interact with the tool.

The 'tool' attribute for the root 'benchmark' nodes of input xml files should be
set to the name of this file without extension, i.e. 'smack_benchexec_driver'.
"""

class Tool(benchexec.tools.template.BaseTool):

    REQUIRED_PATHS = [
                  "corral",
                  "llvm",
                  "lockpwn",
                  "smack"

                  ]

    def executable(self):
        """
        Tells BenchExec to search for 'smack.py' as the main executable to be
        called when running SMACK.
        """
        return util.find_executable('smack')

    def version(self, executable):
        """
        Sets the version number for SMACK, which gets displayed in the "Tool" row
        in BenchExec table headers.
        """
        #return self._version_from_tool(executable).split(' ')[2]
        return "1.5.2"

    def name(self):
        """
        Sets the name for SMACK, which gets displayed in the "Tool" row in
        BenchExec table headers.
        """
        return 'SMACK+Corral'

    def cmdline(self, executable, options, tasks, propertyfile=None, rlimits=
{}):
        """
        Allows us to define special actions to be taken or command line argument
        modifications to make just before calling SMACK.
        """
        assert len(tasks) == 1
        assert propertyfile is not None
        prop = ['--svcomp-property', propertyfile]
        return [executable] + options + prop + tasks

    def determine_result(self, returncode, returnsignal, output, isTimeout):
        """
        Returns a BenchExec result status based on the output of SMACK
        """
        splitout = "\n".join(output)
        if 'SMACK found no errors' in splitout:
            return result.RESULT_TRUE_PROP
        errmsg = re.search(r'SMACK found an error(:\s+([^\.]+))?\.', splitout)
        if errmsg:
          errtype = errmsg.group(2)
          if errtype:
            if 'invalid pointer dereference' == errtype:
              return result.RESULT_FALSE_DEREF
            elif 'invalid memory deallocation' == errtype:
              return result.RESULT_FALSE_FREE
            elif 'memory leak' == errtype:
              return result.RESULT_FALSE_MEMTRACK
            elif 'signed integer overflow' == errtype:
              return result.RESULT_FALSE_OVERFLOW
          else:
            return result.RESULT_FALSE_REACH
        return result.RESULT_UNKNOWN

    def get_value_from_output(self, lines, identifier):
        """
        This function can be referenced in the input xml files (which can define
        additional columns to be displayed in the output tables), and extracts
        additional information from tool output (with the idea that extra
        statistical information would be extracted from tool output, and included
        as a column in the resulting output tables).

        We are using this to generate HTML links for output files, rather than
        parsing output and providing additional statistical data about the run.

        This currently generates a drop-down menu item for the .bc, .bpl,
        generated witness file, and the output from the witness checking tool.

        However, the witness file and checking links are hidden by default, as
        they will not exist if the witness checking pass has not been performed,
        or if the benchmark result was true (in which case there is no trace).
        The visibility of these must be set to visible when witness checking is
        performed for this execution.
        """
        #identifier comes from pattern field of input xml <column> node,
        # which then has variable substitution performed on it first
        #If identifier is the input source file path+name, this will create
        # links in the output table for bpl, bc, and witness related files
        ret = ""
        ret += '<div align="center">\n'
        ret += '  <select onChange="window.location.href=this.value">\n'
        ret += '    <option value=""></option>\n'
        ret += '    <option value="' + identifier + '.bc">.bc</option>\n'
        ret += '    <option value="' + identifier + '.bpl">.bpl</option>\n'
        ret += '    <option value="' + identifier + '.witness.graphml" hidden>Witness Graphml</option>\n'
        ret += '    <option value="' + identifier + '.witnessCheckOutput" hidden>Checker Console</option>\n'
        ret += '    <option value="' + identifier + 'output.log" hidden>Checker Log</option>\n'
        ret += '  </select>\n'
        ret += '</div>\n'
        return ret
