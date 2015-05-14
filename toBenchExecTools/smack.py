import os
import re

import logging
import xml.etree.ElementTree as ET

import benchexec.util as util
import benchexec.tools.template
import benchexec.result as result

#PROGRAM_PATH="bin-2015/smack-corral"

class Tool(benchexec.tools.template.BaseTool):

    def executable(self):
        return util.find_executable('smackverify.py')

    def version(self, executable):
        return '1.5.1dev'

    def name(self):
        return 'SMACK'

    def cmdline(self, executable, options, tasks, propertyfile=None, rlimits={}):
        assert len(tasks) == 1
        return [executable] + \
               [s for s in tasks] + \
               options
        #return [executable] + \
        #       [os.path.relpath(s, start=PROGRAM_PATH) for s in tasks] + \
        #       options

    def get_result(self,output):
        if re.search(r'[1-9]\d* time out|Z3 ran out of resources|z3 timed out', output):
            return 'timeout'
        elif re.search(r'[1-9]\d* verified, 0 errors?|no bugs', output):
            return 'verified'
        elif re.search(r'0 verified, [1-9]\d* errors?|can fail', output):
            return 'error'
        else:
            return 'unknown'

    def determine_result(self, returncode, returnsignal, output, isTimeout):
        res = self.get_result("\n".join(output))

        if res == 'error':
            status = result.RESULT_FALSE_REACH
        elif res == 'verified':
            status = result.RESULT_TRUE_PROP
        else:
            status = result.RESULT_UNKNOWN

        return status
