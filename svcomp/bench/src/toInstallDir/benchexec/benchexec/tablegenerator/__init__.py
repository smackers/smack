"""
BenchExec is a framework for reliable benchmarking.
This file is part of BenchExec.

Copyright (C) 2007-2015  Dirk Beyer
All rights reserved.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
"""

# prepare for Python 3
from __future__ import absolute_import, division, print_function, unicode_literals

import xml.etree.ElementTree as ET
import collections
import os.path
import glob
import json
import argparse
import re
import subprocess
import sys
import time
import tempita

from decimal import *

from .. import __version__
import benchexec.result as result

NAME_START = "results" # first part of filename of table

DEFAULT_OUTPUT_PATH = "results/"

LIB_URL = "http://cdn.jsdelivr.net"
LIB_URL_OFFLINE = "lib/javascript"

TEMPLATE_FILE_NAME = os.path.join(os.path.dirname(__file__), 'template.{format}')
TEMPLATE_FORMATS = ['html', 'csv']
TEMPLATE_ENCODING = 'UTF-8'

DEFAULT_TIME_PRECISION = 3

class Util:
    """
    This Class contains some useful functions for Strings, Files and Lists.
    """

    @staticmethod
    def get_file_list(shortFile, options):
        """
        The function get_file_list expands a short filename to a sorted list
        of filenames. The short filename can contain variables and wildcards.
        """

        # expand tilde and variables
        expandedFile = os.path.expandvars(os.path.expanduser(shortFile))

        # expand wildcards
        fileList = glob.glob(expandedFile)

        # sort alphabetical,
        # if list is emtpy, sorting returns None, so better do not sort
        if len(fileList) != 0:
            fileList.sort()
        else:
            if not options.print_html:
                print ('\nWarning: no file matches "{0}".'.format(shortFile))

        return fileList


    @staticmethod
    def extend_file_list(filelist,options):
        '''
        This function takes a list of files, expands wildcards
        and returns a new list of files.
        '''
        return [file for wildcardFile in filelist for file in Util.get_file_list(wildcardFile,options)]


    @staticmethod
    def split_number_and_unit(s):
        """
        Split a string into two parts: a number prefix and an arbitrary suffix.
        Splitting is done from the end, so the split is where the last digit
        in the string is (that means the prefix may include non-digit characters,
        if they are followed by at least one digit).
        """
        if not s:
            return (s, '')
        pos = len(s)
        while pos and not s[pos-1].isdigit():
            pos -= 1
        return (s[:pos], s[pos:])

    @staticmethod
    def remove_unit(s):
        """
        Remove a unit from a number string, or return the full string if it is not a number.
        """
        (prefix, suffix) = Util.split_number_and_unit(s)
        return suffix if prefix == '' else prefix

    @staticmethod
    def format_number(s, number_of_digits):
        """
        If the value is a number (or number plus one char),
        this function returns a string-representation of the number
        with a number of digits after the decimal separator.
        If the number has more digits, it is rounded, else zeros are added.

        If the value is no number, it is returned unchanged.
        """
        # if the number ends with "s" or another unit, remove it
        value, suffix = Util.split_number_and_unit((str(s) or '').strip())
        try:
            floatValue = float(value)
            return "{value:.{width}f}{suffix}".format(width=number_of_digits, value=floatValue, suffix=suffix)
        except ValueError: # if value is no float, don't format it
            return s


    @staticmethod
    def format_value(value, column):
        """
        Format a value nicely for human-readable output (including rounding).
        """
        if not value:
            return '-'

        number_of_digits = column.number_of_digits
        if number_of_digits is None and column.title.lower().endswith('time'):
            number_of_digits = DEFAULT_TIME_PRECISION

        if number_of_digits is None:
            return value
        return Util.format_number(value, number_of_digits)


    @staticmethod
    def to_decimal(s):
        # remove whitespaces and trailing units (e.g., in '1.23s')
        s, _ = Util.split_number_and_unit((s or '').strip())
        return Decimal(s) if s else Decimal()


    @staticmethod
    def collapse_equal_values(values, counts):
        """
        Take a tuple (values, counts), remove consecutive values and increment their count instead.
        """
        assert len(values) == len(counts)
        previousValue = values[0]
        previousCount = 0

        for value, count in zip(values, counts):
            if value != previousValue:
                yield (previousValue, previousCount)
                previousCount = 0
                previousValue = value
            previousCount += count

        yield (previousValue, previousCount)

    @staticmethod
    def get_column_value(sourcefileTag, columnTitle, default=None):
        for column in sourcefileTag.findall('column'):
            if column.get('title') == columnTitle:
                    return column.get('value')
        return default

    @staticmethod
    def flatten(list):
        return [value for sublist in list for value in sublist]

    @staticmethod
    def json(obj):
        return tempita.html(json.dumps(obj))

    @staticmethod
    def prettylist(list):
        if not list:
            return ''

        # Filter out duplicate values while keeping order
        values = set()
        uniqueList = []
        for entry in list:
            if not entry in values:
                values.add(entry)
                uniqueList.append(entry)

        return uniqueList[0] if len(uniqueList) == 1 \
            else '[' + '; '.join(uniqueList) + ']'

def parse_table_definition_file(file, all_columns, options):
    '''
    This function parses the input to get run sets and columns.
    The param 'file' is an XML file defining the result files and columns.

    If column titles are given in the XML file,
    they will be searched in the result files.
    If no title is given, all columns of the result file are taken.

    @return: a list of RunSetResult objects
    '''
    if not options.print_html:
        print ("reading table definition from '{0}'...".format(file))
    if not os.path.isfile(file):
        print ('File {0!r} does not exist.'.format(file))
        exit()

    def extract_columns_from_table_definition_file(xmltag):
        """
        Extract all columns mentioned in the result tag of a table definition file.
        """
        return [Column(c.get("title"), c.text, c.get("numberOfDigits"))
                for c in xmltag.findall('column')]

    runSetResults = []
    tableGenFile = ET.ElementTree().parse(file)
    if 'table' != tableGenFile.tag:
        print ("ERROR:\n" \
            + "    The XML file seems to be invalid.\n" \
            + "    The rootelement of table-definition-file is not named 'table'.")
        exit()

    defaultColumnsToShow = extract_columns_from_table_definition_file(tableGenFile)

    base_dir = os.path.dirname(file)

    def getResultTags(rootTag, options):
        tags = rootTag.findall('result')
        if not tags:
            tags = rootTag.findall('test')
            if tags and not options.print_html:
                print("Warning: file {0} contains deprecated 'test' tags, rename them to 'result'".format(file))
        return tags

    for resultTag in getResultTags(tableGenFile):
        if not 'filename' in resultTag.attrib:
            if not options.print_html:
                print('Result tag without filename attribute in {0}.'.format(file))
            continue
        columnsToShow = extract_columns_from_table_definition_file(resultTag) or defaultColumnsToShow
        filelist = Util.get_file_list(os.path.join(base_dir, resultTag.get('filename')), options) # expand wildcards
        runSetResults += [RunSetResult.create_from_xml(resultsFile, parse_results_file(resultsFile, options), options, columnsToShow, all_columns) for resultsFile in filelist]

    for unionTag in tableGenFile.findall('union'):
        columnsToShow = extract_columns_from_table_definition_file(unionTag) or defaultColumnsToShow
        result = RunSetResult([], collections.defaultdict(list), columnsToShow)

        for resultTag in getResultTags(unionTag):
            if not 'filename' in resultTag.attrib:
                if not options.print_html:
                    print('Result tag without filename attribute in {0}.'.format(file))
                continue
            filelist = Util.get_file_list(os.path.join(base_dir, resultTag.get('filename')), options) # expand wildcards
            for resultsFile in filelist:
                result.append(resultsFile, parse_results_file(resultsFile, options), all_columns)

        if result.filelist:
            name = unionTag.get('title', unionTag.get('name'))
            if name:
                result.attributes['name'] = [name]
            runSetResults.append(result)

    return runSetResults


def get_task_id(task):
    """
    Return a unique identifier for a given task.
    @param task: the XML element that represents a task
    @return a tuple with filename of task as first element
    """
    if 'properties' in task.keys():
        return (task.get('name'), task.get('properties'))
    else:
        return (task.get('name'), )


class Column:
    """
    The class Column contains title, pattern (to identify a line in log_file),
    and number_of_digits of a column.
    It does NOT contain the value of a column.
    """
    def __init__(self, title, pattern, numOfDigits):
        self.title = title
        self.pattern = pattern
        self.number_of_digits = numOfDigits


class RunSetResult():
    """
    The Class RunSetResult contains all the results of one execution of a run set:
    the sourcefiles tags (with sourcefiles + values), the columns to show
    and the benchmark attributes.
    """
    def __init__(self, filelist, attributes, columns, options, summary={}):
        self.filelist = filelist
        self.attributes = attributes
        self.columns = columns
        self.summary = summary
        self.options = options

    def get_tasks(self):
        return list(map(get_task_id, self.filelist))

    def append(self, resultFile, resultElem, all_columns=False):
        self.filelist += _get_run_tags_from_xml(resultElem)
        for attrib, values in RunSetResult._extract_attributes_from_result(resultFile, resultElem).items():
            self.attributes[attrib].extend(values)

        if not self.columns:
            self.columns = RunSetResult._extract_existing_columns_from_result(resultFile, resultElem, all_columns,self.options)

    @staticmethod
    def create_from_xml(resultFile, resultElem, options, columns=None, all_columns=False):
        '''
        This function extracts everything necessary for creating a RunSetResult object
        from the "result" XML tag of a benchmark result file.
        It returns a RunSetResult object.
        '''
        attributes = RunSetResult._extract_attributes_from_result(resultFile, resultElem)

        if not columns:
            columns = RunSetResult._extract_existing_columns_from_result(resultFile, resultElem, all_columns, options)

        summary = RunSetResult._extract_summary_from_result(resultElem, columns)

        return RunSetResult(_get_run_tags_from_xml(resultElem),
                attributes, columns, summary)

    @staticmethod
    def _extract_existing_columns_from_result(resultFile, resultElem, all_columns, options):
        run_results = _get_run_tags_from_xml(resultElem)
        if not run_results:
            if not options.print_html:
                print("Empty resultfile found: " + resultFile)
            return []
        else: # show all available columns
            columnNames = set()
            columns = []
            for s in run_results:
                for c in s.findall('column'):
                    title = c.get('title')
                    if not title in columnNames \
                            and (all_columns or c.get('hidden') != 'true'):
                        columnNames.add(title)
                        columns.append(Column(title, None, None))
            return columns


    @staticmethod
    def _extract_attributes_from_result(resultFile, resultTag):
        attributes = collections.defaultdict(list)

        # Defaults
        attributes['name'  ] = [resultTag.get('benchmarkname')]
        attributes['branch'] = [os.path.basename(resultFile).split('#')[0] if '#' in resultFile else '']

        # Update with real values
        for attrib, value in resultTag.attrib.items():
            attributes[attrib] = [value]

        # Add system information if present
        for systemTag in resultTag.findall('systeminfo'):
            cpuTag = systemTag.find('cpu')
            attributes['os'   ].append(systemTag.find('os').get('name'))
            attributes['cpu'  ].append(cpuTag.get('model'))
            attributes['cores'].append( cpuTag.get('cores'))
            attributes['freq' ].append(cpuTag.get('frequency'))
            attributes['ram'  ].append(systemTag.find('ram').get('size'))
            attributes['host' ].append(systemTag.get('hostname', 'unknown'))

        return attributes
    
    @staticmethod
    def _extract_summary_from_result(resultTag, columns):
        summary = collections.defaultdict(list)

        # Add summary for columns if present
        for column in resultTag.findall('column'):
            title = column.get('title')
            if title in (c.title for c in columns):
                summary[title] = column.get('value')

        return summary


def _get_run_tags_from_xml(result_elem):
    return result_elem.findall('run') + result_elem.findall('sourcefile')


def parse_results_file(resultFile, options):
    '''
    This function parses a XML file with the results of the execution of a run set.
    It returns the "result" XML tag
    '''
    if not os.path.isfile(resultFile):
        print ('File {0!r} is not found.'.format(resultFile))
        exit()

    if not options.print_html:
        print ('    ' + resultFile)

    resultElem = ET.ElementTree().parse(resultFile)

    if resultElem.tag not in ['result', 'test']:
        print (("ERROR:\n" \
            + "XML file with benchmark results seems to be invalid.\n" \
            + "The root element of the file is not named 'result' or 'test'.\n" \
            + "If you want to run a table-definition file,\n"\
            + "you should use the option '-x' or '--xml'.").replace('\n','\n    '))
        exit()

    insert_logfile_names(resultFile, resultElem)
    return resultElem

def insert_logfile_names(resultFile, resultElem):
    # get folder of logfiles (truncate end of XML file name and append .logfiles instead)
    log_folder = resultFile[0:resultFile.rfind('.results.')] + '.logfiles/'

    # append begin of filename
    runSetName = resultElem.get('name')
    if runSetName is not None:
        blockname = resultElem.get('block')
        if blockname is None:
            log_folder += runSetName + "."
        elif blockname == runSetName:
            pass # real runSetName is empty
        else:
            assert runSetName.endswith("." + blockname)
            runSetName = runSetName[:-(1 + len(blockname))] # remove last chars
            log_folder += runSetName + "."

    # for each file: append original filename and insert log_file_name into sourcefileElement
    for sourcefile in _get_run_tags_from_xml(resultElem):
        log_file_name = os.path.basename(sourcefile.get('name')) + ".log"
        sourcefile.set('logfile', log_folder + log_file_name)


def merge_tasks(runset_results, options):
    """
    This function merges the filelists of all RunSetResult objects.
    If necessary, it can merge lists of names: [A,C] + [A,B] --> [A,B,C]
    and add dummy elements to the filelists.
    It also ensures the same order of files.
    Returns a list of task ids.
    """
    task_list = []
    task_set = set()
    for result in runset_results:
        index = -1
        currentresult_taskset = set()
        for task in result.get_tasks():
            if task in currentresult_taskset:
                if not options.print_html:
                    print ("File {0} is present twice, skipping it.".format(task[0]))
            else:
                currentresult_taskset.add(task)
                if task not in task_set:
                    task_list.insert(index+1, task)
                    task_set.add(task)
                    index += 1
                else:
                    index = task_list.index(task)

    merge_task_lists(runset_results, task_list, options)
    return task_list

def merge_task_lists(runset_results, tasks, options):
    """
    Set the filelists of all RunSetResult elements so that they contain the same files
    in the same order. For missing files a dummy element is inserted.
    """
    for result in runset_results:
        # create mapping from id to run tag
        dic = dict([(get_task_id(task), task) for task in result.filelist])
        result.filelist = [] # clear and repopulate filelist
        for task in tasks:
            task_result = dic.get(task)
            if task_result is None:
                task_result = ET.Element('run') # create an empty dummy element
                task_result.set('logfile', None)
                task_result.set('name', task[0])
                if not options.print_html:
                    print ('    no result for {0}'.format(task[0]))
            result.filelist.append(task_result)


def find_common_tasks(runset_results, options):
    tasks_in_first_runset = runset_results[0].get_tasks()

    task_set = set(tasks_in_first_runset)
    for result in runset_results:
        task_set = task_set & set(result.get_tasks())

    task_list = []
    if not task_set:
        if not options.print_html:
            print('No files are present in all benchmark results.')
    else:
        task_list = [task for task in tasks_in_first_runset if task in task_set]
        merge_task_lists(runset_results, task_list, options)

    return task_list


class RunResult:
    """
    The class RunResult contains the results of a single verification run.
    """
    def __init__(self, status, category, log_file, columns, values):
        assert(len(columns) == len(values))
        self.status = status
        self.log_file = log_file
        self.columns = columns
        self.values = values
        self.category = category

    @staticmethod
    def create_from_xml(sourcefileTag, get_value_from_logfile, options, listOfColumns, correct_only):
        '''
        This function collects the values from one run.
        Only columns that should be part of the table are collected.
        '''

        def read_logfile_lines(logfilename):
            if not logfilename: return []
            try:
                with open(logfilename, 'rt') as logfile:
                    return logfile.readlines()
            except IOError as e:
                if not options.print_html:
                    print('WARNING: Could not read value from logfile: {}'.format(e))
                return []

        status = Util.get_column_value(sourcefileTag, 'status', '')
        category = Util.get_column_value(sourcefileTag, 'category', 'missing')
        score = result.calculate_score(category, status)
        logfileLines = None

        values = []

        for column in listOfColumns: # for all columns that should be shown
            value = None # default value
            if column.title.lower() == 'score':
                value = str(score)
            elif column.title.lower() == 'status':
                value = status

            elif not correct_only or score > 0:
                if not column.pattern: # collect values from XML
                    value = Util.get_column_value(sourcefileTag, column.title)

                else: # collect values from logfile
                    if logfileLines is None: # cache content
                        logfileLines = read_logfile_lines(sourcefileTag.get('logfile'))

                    value = get_value_from_logfile(logfileLines, column.pattern)

            if column.number_of_digits is not None:
                value = Util.format_number(value, column.number_of_digits)

            values.append(value)

        return RunResult(status, category, sourcefileTag.get('logfile'), listOfColumns, values)


class Row:
    """
    The class Row contains all the results for one sourcefile (a list of RunResult instances).
    It is identified by the name of the source file and optional additional data
    (such as the property).
    It corresponds to one complete row in the final tables.
    """
    def __init__(self, task_id):
        self.id = task_id
        self.filename = task_id[0]
        self.properties = task_id[1] if len(task_id) > 1 else None
        self.results = []

    def add_run_result(self, runresult):
        self.results.append(runresult)

    def set_relative_path(self, common_prefix, base_dir):
        """
        generate output representation of rows
        """
        # make path relative to directory of output file if necessary
        self.file_path = self.filename if os.path.isabs(self.filename) \
                                 else os.path.relpath(self.filename, base_dir)

        self.short_filename = self.filename.replace(common_prefix, '', 1)

def rows_to_columns(rows):
    """
    Convert a list of Rows into a column-wise list of list of RunResult
    """
    return zip(*[row.results for row in rows])


def get_rows(runSetResults, task_ids, correct_only, options):
    """
    Create list of rows with all data. Each row consists of several RunResults.
    """

    def load_tool(result, options):
        """
        Load the module with the tool-specific code.
        """
        tool_module = result.attributes['toolmodule'][0] if 'toolmodule' in result.attributes else None
        if not tool_module:
            if not options.print_html:
                print('Cannot extract values from log files for benchmark results {0} (missing attribute "toolmodule" on tag "result").'.format(
                    Util.prettylist(result.attributes['name'])))
            return None
        try:
            return __import__(tool_module, fromlist=['Tool']).Tool()
        except ImportError as ie:
            if not options.print_html:
                print('Missing module "{0}", cannot extract values from log files (ImportError: {1}).'.format(tool_module, ie))
        except AttributeError:
            if not options.print_html:
                print('The module "{0}" does not define the necessary class Tool, cannot extract values from log files.'.format(tool_module))
        return None

    rows = [Row(task_id) for task_id in task_ids]

    # get values for each run set
    for result in runSetResults:

        def get_value_from_logfile(lines, identifier):
            """
            This method searches for values in lines of the content.
            It uses a tool-specific method to so.
            """
            # store tool instance lazily in attribute of the function to load it only once
            if not 'tool' in get_value_from_logfile.__dict__:
                get_value_from_logfile.tool = load_tool(result)

            if get_value_from_logfile.tool:
                return get_value_from_logfile.tool.get_value_from_output(lines, identifier)
            else:
                return None

        # get values for each file in a run set
        for fileResult, row in zip(result.filelist, rows):
            row.add_run_result(RunResult.create_from_xml(
                    fileResult,
                    get_value_from_logfile,
                    options,
                    result.columns,
                    correct_only))

    return rows


def filter_rows_with_differences(rows, options):
    """
    Find all rows with differences in the status column.
    """
    if not rows:
        # empty table
        return []
    if len(rows[0].results) == 1:
        # table with single column
        return []

    def all_equal_result(listOfResults):
        allStatus = set([result.status for result in listOfResults if result.status])
        return len(allStatus) <= 1

    rowsDiff = [row for row in rows if not all_equal_result(row.results)]

    if len(rowsDiff) == 0 and not options.print_html:
        print ("---> NO DIFFERENCE FOUND IN COLUMN 'STATUS'")
    elif len(rowsDiff) == len(rows) and not options.print_html:
        print ("---> DIFFERENCES FOUND IN ALL ROWS, NO NEED TO CREATE DIFFERENCE TABLE")
        return []

    return rowsDiff



def get_table_head(runSetResults, commonFileNamePrefix):

    # This list contains the number of columns each run set has
    # (the width of a run set in the final table)
    # It is used for calculating the column spans of the header cells.
    runSetWidths = [len(runSetResult.columns) for runSetResult in runSetResults]

    for runSetResult in runSetResults:
        # Ugly because this overwrites the entries in the map,
        # but we don't need them anymore and this is the easiest way
        for key in runSetResult.attributes:
            runSetResult.attributes[key] = Util.prettylist(runSetResult.attributes[key])

    def get_row(rowName, format, collapse=False, onlyIf=None, default='Unknown'):
        def format_cell(attributes):
            if onlyIf and not onlyIf in attributes:
                formatStr = default
            else:
                formatStr = format
            return formatStr.format(**attributes)

        values = [format_cell(runSetResult.attributes) for runSetResult in runSetResults]
        if not any(values): return None # skip row without values completely

        valuesAndWidths = list(Util.collapse_equal_values(values, runSetWidths)) \
                          if collapse else list(zip(values, runSetWidths))

        return tempita.bunch(id=rowName.lower().split(' ')[0],
                             name=rowName,
                             content=valuesAndWidths)

    benchmarkNames = [runSetResult.attributes['benchmarkname'] for runSetResult in runSetResults]
    allBenchmarkNamesEqual = benchmarkNames.count(benchmarkNames[0]) == len(benchmarkNames)

    titles      = [column.title for runSetResult in runSetResults for column in runSetResult.columns]
    runSetWidths1 = [1]*sum(runSetWidths)
    titleRow    = tempita.bunch(id='columnTitles', name=commonFileNamePrefix,
                                content=list(zip(titles, runSetWidths1)))

    return {'tool':    get_row('Tool', '{tool} {version}', collapse=True),
            'limit':   get_row('Limits', 'timelimit: {timelimit}, memlimit: {memlimit}, CPU core limit: {cpuCores}', collapse=True),
            'host':    get_row('Host', '{host}', collapse=True, onlyIf='host'),
            'os':      get_row('OS', '{os}', collapse=True, onlyIf='os'),
            'system':  get_row('System', 'CPU: {cpu} with {cores} cores, frequency: {freq}; RAM: {ram}', collapse=True, onlyIf='cpu'),
            'date':    get_row('Date of execution', '{date}', collapse=True),
            'runset':  get_row('Run set', '{name}' if allBenchmarkNamesEqual else '{benchmarkname}.{name}'),
            'branch':  get_row('Branch', '{branch}'),
            'options': get_row('Options', '{options}'),
            'property':get_row('Propertyfile', '{propertyfiles}', collapse=True, onlyIf='propertyfiles', default=''),
            'title':   titleRow}


def get_stats(rows, options):
    stats = [get_stats_of_run_set(runResults, options) for runResults in rows_to_columns(rows)] # column-wise
    rowsForStats = list(map(Util.flatten, zip(*stats))) # row-wise

    # Calculate maximal score and number of true/false files for the given properties
    count_true = count_false = 0
    for row in rows:
        if not row.properties:
            # properties missing for at least one task, result would be wrong
            count_true = count_false = 0
            if not options.print_html:
                print('Missing property for ' + row.filename)
            break
        correct_result = result.satisfies_file_property(row.filename, row.properties.split())
        if correct_result is True:
            count_true += 1
        elif correct_result is False:
            count_false += 1
    max_score = count_true * result.SCORE_CORRECT_TRUE + count_false * result.SCORE_CORRECT_FALSE

    if max_score:
        score_row = tempita.bunch(default=None, id='score',
                                  title='score ({0} tasks, max score: {1})'.format(len(rows), max_score),
                                  description='{0} true files, {1} false files'.format(count_true, count_false),
                                  content=rowsForStats[7])
    else:
        score_row = tempita.bunch(default=None, id='score',
                                  title='score ({0} tasks)'.format(len(rows)),
                                  content=rowsForStats[7])

    def indent(n):
        return '&nbsp;'*(n*4)

    return [tempita.bunch(default=None, title='total tasks', content=rowsForStats[0]),
            tempita.bunch(default=None, title=indent(1)+'correct results', description='(property holds + result is true) OR (property does not hold + result is false)', content=rowsForStats[1]),
            tempita.bunch(default=None, title=indent(2)+'correct true', description='property holds + result is true', content=rowsForStats[2]),
            tempita.bunch(default=None, title=indent(2)+'correct false', description='property does not hold + result is false', content=rowsForStats[3]),
            tempita.bunch(default=None, title=indent(1)+'incorrect results', description='(property holds + result is false) OR (property does not hold + result is true)', content=rowsForStats[4]),
            tempita.bunch(default=None, title=indent(2)+'incorrect true', description='property does not hold + result is true', content=rowsForStats[5]),
            tempita.bunch(default=None, title=indent(2)+'incorrect false', description='property holds + result is false', content=rowsForStats[6]),
            score_row,
            ]


def get_stats_of_run_set(runResults, options):
    """
    This function returns the numbers of the statistics.
    @param runResults: All the results of the execution of one run set (as list of RunResult objects)
    """

    # convert:
    # [['TRUE', 0,1], ['FALSE', 0,2]] -->  [['TRUE', 'FALSE'], [0,1, 0,2]]
    # in python2 this is a list, in python3 this is the iterator of the list
    # this works, because we iterate over the list some lines below
    listsOfValues = zip(*[runResult.values for runResult in runResults])

    columns = runResults[0].columns
    statusList = [(runResult.category, runResult.status) for runResult in runResults]

    # collect some statistics
    sumRow = []
    correctRow = []
    correctTrueRow = []
    correctFalseRow = []
    incorrectRow = []
    wrongTrueRow = []
    wrongFalseRow = []
    scoreRow = []

    for column, values in zip(columns, listsOfValues):
        if column.title == 'status':
            countCorrectTrue, countCorrectFalse, countWrongTrue, countWrongFalse, countMissing = get_category_count(statusList)

            sum     = StatValue(len([status for (category, status) in statusList if status]))
            correct = StatValue(countCorrectTrue + countCorrectFalse)
            correctTrue = StatValue(countCorrectTrue)
            correctFalse = StatValue(countCorrectFalse)
            score   = StatValue(result.SCORE_CORRECT_TRUE   * countCorrectTrue + \
                                result.SCORE_CORRECT_FALSE * countCorrectFalse + \
                                result.SCORE_WRONG_TRUE     * countWrongTrue + \
                                result.SCORE_WRONG_FALSE   * countWrongFalse,
                                )
            incorrect = StatValue(countWrongTrue + countWrongFalse)
            wrongTrue   = StatValue(countWrongTrue)
            wrongFalse = StatValue(countWrongFalse)

        else:
            sum, correct, correctTrue, correctFalse, incorrect, wrongTrue, wrongFalse = get_stats_of_number_column(values, statusList, column.title, options)
            score = ''

        if (sum.sum, correct.sum, correctTrue.sum, correctFalse.sum, incorrect.sum, wrongTrue.sum, wrongFalse.sum) == (0,0,0,0,0,0,0):
            (sum, correct, correctTrue, correctFalse, incorrect, wrongTrue, wrongFalse) = (None, None, None, None, None, None, None)

        sumRow.append(sum)
        correctRow.append(correct)
        correctTrueRow.append(correctTrue)
        correctFalseRow.append(correctFalse)
        incorrectRow.append(incorrect)
        wrongTrueRow.append(wrongTrue)
        wrongFalseRow.append(wrongFalse)
        scoreRow.append(score)

    def replace_irrelevant(row):
        if not row:
            return
        count = row[0]
        if not count or not count.sum:
            for i in range(1, len(row)):
                row[i] = None

    replace_irrelevant(sumRow)
    replace_irrelevant(correctRow)
    replace_irrelevant(correctTrueRow)
    replace_irrelevant(correctFalseRow)
    replace_irrelevant(incorrectRow)
    replace_irrelevant(wrongTrueRow)
    replace_irrelevant(wrongFalseRow)
    replace_irrelevant(scoreRow)

    return (sumRow, correctRow, correctTrueRow, correctFalseRow, incorrectRow, wrongTrueRow, wrongFalseRow, scoreRow)


class StatValue:
    def __init__(self, sum, min=None, max=None, avg=None, median=None):
        self.sum = sum
        self.min = min
        self.max = max
        self.avg = avg
        self.median = median

    def __str__(self):
        return str(self.sum)

    @classmethod
    def from_list(cls, values):
        if not values:
            return StatValue(0)

        return StatValue(sum(values),
                         min    = min(values),
                         max    = max(values),
                         avg    = float("{:.3f}".format(sum(values) / len(values))),
                         median = sorted(values)[len(values)//2],
                         )


def get_category_count(categoryList):
    # count different elems in statusList
    counts = collections.defaultdict(int)
    for category in categoryList:
        counts[category] += 1

    # warning: read next lines carefully, there are some brackets and commas!
    return (
        # correctTrue, correctFalse
            counts[result.CATEGORY_CORRECT, result.RESULT_TRUE_PROP],
            counts[result.CATEGORY_CORRECT, result.RESULT_FALSE_REACH] \
          + counts[result.CATEGORY_CORRECT, result.RESULT_FALSE_DEREF] \
          + counts[result.CATEGORY_CORRECT, result.RESULT_FALSE_FREE] \
          + counts[result.CATEGORY_CORRECT, result.RESULT_FALSE_MEMTRACK] \
          + counts[result.CATEGORY_CORRECT, result.RESULT_FALSE_TERMINATION],

        # wrongTrue, wrongFalse
            counts[result.CATEGORY_WRONG, result.RESULT_TRUE_PROP],
            counts[result.CATEGORY_WRONG, result.RESULT_FALSE_REACH] \
          + counts[result.CATEGORY_WRONG, result.RESULT_FALSE_DEREF] \
          + counts[result.CATEGORY_WRONG, result.RESULT_FALSE_FREE] \
          + counts[result.CATEGORY_WRONG, result.RESULT_FALSE_MEMTRACK] \
          + counts[result.CATEGORY_WRONG, result.RESULT_FALSE_TERMINATION],

        # missing
            counts[result.CATEGORY_MISSING, result.RESULT_TRUE_PROP] \
          + counts[result.CATEGORY_MISSING, result.RESULT_FALSE_REACH] \
          + counts[result.CATEGORY_MISSING, result.RESULT_FALSE_DEREF] \
          + counts[result.CATEGORY_MISSING, result.RESULT_FALSE_FREE] \
          + counts[result.CATEGORY_MISSING, result.RESULT_FALSE_MEMTRACK] \
          + counts[result.CATEGORY_MISSING, result.RESULT_FALSE_TERMINATION] \
            )


def get_stats_of_number_column(values, categoryList, columnTitle, options):
    assert len(values) == len(categoryList)
    try:
        valueList = [Util.to_decimal(v) for v in values]
    except InvalidOperation as e:
        if columnTitle != "host" and not options.print_html: # we ignore values of column host, used in cloud-mode
            print("Warning: {0}. Statistics may be wrong.".format(e))
        return (StatValue(0), StatValue(0), StatValue(0), StatValue(0), StatValue(0), StatValue(0), StatValue(0))

    valuesPerCategory = collections.defaultdict(list)
    for value, catStat in zip(valueList, categoryList):
        category, status = catStat
        if status.startswith(result.STR_FALSE):
            status = result.STR_FALSE # ignore exact status, we do not need it
        valuesPerCategory[category, status].append(value)

    return (StatValue.from_list(valueList),
            StatValue.from_list(valuesPerCategory[result.CATEGORY_CORRECT, result.RESULT_TRUE_PROP]
                              + valuesPerCategory[result.CATEGORY_CORRECT, result.STR_FALSE]),
            StatValue.from_list(valuesPerCategory[result.CATEGORY_CORRECT, result.RESULT_TRUE_PROP]),
            StatValue.from_list(valuesPerCategory[result.CATEGORY_CORRECT, result.STR_FALSE]),
            StatValue.from_list(valuesPerCategory[result.CATEGORY_WRONG, result.RESULT_TRUE_PROP]
                              + valuesPerCategory[result.CATEGORY_WRONG, result.STR_FALSE]),
            StatValue.from_list(valuesPerCategory[result.CATEGORY_WRONG, result.RESULT_TRUE_PROP]),
            StatValue.from_list(valuesPerCategory[result.CATEGORY_WRONG, result.STR_FALSE]),
            )


def get_regression_count(rows, ignoreFlappingTimeouts): # for options.dump_counts

    columns = list(rows_to_columns(rows))
    if len(columns) < 2:
        return 0 # no regressions with only one run

    timeouts = set()
    for runResults in columns[:-1]:
        timeouts |= set(index for (index, runResult) in enumerate(runResults) if runResult.status == 'TIMEOUT')

    def is_flapping_timeout(index, oldResult, newResult):
        return index in timeouts \
            and oldResult.status != 'TIMEOUT' \
            and newResult.status == 'TIMEOUT'

    def ignore_regression(oldResult, newResult):
        return oldResult.status == 'TIMEOUT' and newResult.status == 'OUT OF MEMORY' \
            or oldResult.status == 'OUT OF MEMORY' and newResult.status == 'TIMEOUT'

    regressions = 0
    for index, (oldResult, newResult) in enumerate(zip(columns[-2], columns[-1])):
        # regression can be only if result is different and new result is not correct
        if oldResult.status != newResult.status and newResult.category != result.CATEGORY_CORRECT:

            if not (ignoreFlappingTimeouts and is_flapping_timeout(index, oldResult, newResult)) \
                    and not ignore_regression(oldResult, newResult):
                regressions += 1
    return regressions


def get_counts(rows): # for options.dump_counts
    countsList = []

    for runResults in rows_to_columns(rows):
        statusList = [(runResult.category, runResult.status) for runResult in runResults]
        correctTrue, correctFalse, wrongTrue, wrongFalse, missing = get_category_count(statusList)

        correct = correctTrue + correctFalse
        wrong = wrongTrue + wrongFalse
        unknown = len(statusList) - correct - wrong - missing

        countsList.append((correct, wrong, unknown))

    return countsList


def get_summary(runSetResults):
    summaryStats = []
    available = False
    for runSetResult in runSetResults:
        for column in runSetResult.columns:
            if column.title in runSetResult.summary and runSetResult.summary[column.title] != '':
                available = True
                value = runSetResult.summary[column.title]
            else:
                value = ''
            summaryStats.append(StatValue(value))

    if available:
        return tempita.bunch(default=None, title='local summary', 
            description='(This line contains some statistics from local execution. Only trust those values, if you use your own computer.)',
            content=summaryStats)
    else:
        return None


def create_tables(name, runSetResults, task_ids, rows, rowsDiff, outputPath, outputFilePattern, options):
    '''
    create tables and write them to files
    '''

    # get common folder of sourcefiles
    common_prefix = os.path.commonprefix(list(map(lambda x : x[0], task_ids))) # maybe with parts of filename
    common_prefix = common_prefix[: common_prefix.rfind('/') + 1] # only foldername
    list(map(lambda row: Row.set_relative_path(row, common_prefix, outputPath), rows))

    head = get_table_head(runSetResults, common_prefix)
    run_sets_data = [runSetResult.attributes for runSetResult in runSetResults]
    run_sets_columns = [[column for column in runSet.columns] for runSet in runSetResults]
    run_sets_column_titles = [[column.title for column in runSet.columns] for runSet in runSetResults]

    templateNamespace={'flatten': Util.flatten,
                       'json': Util.json,
                       'relpath': os.path.relpath,
                       'format_value': Util.format_value,
                       'split_number_and_unit': Util.split_number_and_unit,
                       'remove_unit': Util.remove_unit,
                       }

    def write_table(type, title, rows, options):
        stats = get_stats(rows, options)

        summary = get_summary(runSetResults)
        if summary and type != 'diff' and not options.correct_only and not options.common:
            stats.insert(1, summary)

        for format in TEMPLATE_FORMATS:
            outfile = os.path.join(outputPath, outputFilePattern.format(name=name, type=type, ext=format))
            if not options.print_html:
                print ('writing {0} into {1} ...'.format(format.upper().ljust(4), outfile))

            # read template
            Template = tempita.HTMLTemplate if format == 'html' else tempita.Template
            template_file = TEMPLATE_FILE_NAME.format(format=format)
            try:
                template_content = __loader__.get_data(template_file).decode(TEMPLATE_ENCODING)
            except NameError:
                with open(template_file, mode='r') as f:
                    template_content = f.read()
            template = Template(template_content, namespace=templateNamespace)

            # write file
            outStr = template.substitute(title=title,
                                         head=head,
                                         body=rows,
                                         foot=stats,
                                         run_sets=run_sets_data,
                                         columns=run_sets_columns,
                                         columnTitles=run_sets_column_titles,
                                         lib_url=options.lib_url,
                                         base_dir=outputPath)
            if not options.print_html:
                with open(outfile, 'w') as file:
                    file.write(outStr)
            elif format == 'html':
                print(outStr)

            if options.show_table and format == 'html' and not options.print_html:
                try:
                    with open(os.devnull, 'w') as devnull:
                        subprocess.Popen(['xdg-open', outfile],
                                         stdout=devnull, stderr=devnull)
                except OSError:
                    pass

    # write normal tables
    write_table("table", name, rows, options)

    # write difference tables
    if rowsDiff:
        write_table("diff", name + " differences", rowsDiff, options)

def basename_without_ending(file):
    name = os.path.basename(file)
    if name.endswith(".xml"):
        name = name[:-4]
    return name

def main(args=None):

    if args is None:
        args = sys.argv

    parser = argparse.ArgumentParser(
        fromfile_prefix_chars='@',
        description=
        """Create tables with the results of one or more benchmark executions.
           Command-line parameters can additionally be read from a file if file name prefixed with '@' is given as argument.
           Part of BenchExec: https://github.com/dbeyer/benchexec/"""
    )

    parser.add_argument("tables",
        metavar="RESULT",
        type=str,
        nargs='*',
        help="XML file with the results from the benchmark script"
    )
    parser.add_argument("-x", "--xml",
        action="store",
        type=str,
        dest="xmltablefile",
        help="XML file with the table definition."
    )
    parser.add_argument("-o", "--outputpath",
        action="store",
        type=str,
        dest="outputPath",
        help="Output path for the tables."
    )
    parser.add_argument("-n", "--name",
        action="store",
        type=str,
        dest="output_name",
        help="Base name of the created output files."
    )
    parser.add_argument("--ignore-erroneous-benchmarks",
        action="store_true",
        dest="ignore_errors",
        help="Ignore results where the was an error during benchmarking."
    )
    parser.add_argument("-d", "--dump",
        action="store_true", dest="dump_counts",
        help="Print summary statistics for regressions and the good, bad, and unknown counts."
    )
    parser.add_argument("--ignore-flapping-timeout-regressions",
        action="store_true", dest="ignoreFlappingTimeouts",
        help="For the regression-count statistics, do not count regressions to timeouts if the file already had timeouts before."
    )
    parser.add_argument("-c", "--common",
        action="store_true", dest="common",
        help="Put only sourcefiles into the table for which all benchmarks contain results."
    )
    parser.add_argument("--no-diff",
        action="store_false", dest="write_diff_table",
        help="Do not output a table with result differences between benchmarks."
    )
    parser.add_argument("--correct-only",
        action="store_true", dest="correct_only",
        help="Clear all results (e.g., time) in cases where the result was not correct."
    )
    parser.add_argument("--all-columns",
        action="store_true", dest="all_columns",
        help="Show all columns in tables, including those that are normally hidden."
    )
    parser.add_argument("--offline",
        action="store_const", dest="lib_url",
        const=LIB_URL_OFFLINE,
        default=LIB_URL,
        help="Don't insert links to http://www.sosy-lab.org, instead expect JS libs in libs/javascript."
    )
    parser.add_argument("--show",
        action="store_true", dest="show_table",
        help="Open the produced HTML table(s) in the default browser."
    )
    parser.add_argument("--printHTML",
        action="store_true", dest="print_html",
        help="Prints html output to stdout for use in dynamic pages"
    )
    parser.add_argument("--version",
        action="version", version="%(prog)s " + __version__
    )

    options = parser.parse_args(args[1:])

    name = options.output_name
    outputPath = options.outputPath
    outputFilePattern = "{name}.{type}.{ext}"

    if options.xmltablefile:
        if options.tables:
            print ("Invalid additional arguments '{}'".format(" ".join(options.tables)))
            exit()
        runSetResults = parse_table_definition_file(options.xmltablefile, options.all_columns)
        if not name:
            name = basename_without_ending(options.xmltablefile)

        if not outputPath:
            outputPath = os.path.dirname(options.xmltablefile)

    else:
        if options.tables:
            inputFiles = options.tables
        else:
            searchDir = outputPath or DEFAULT_OUTPUT_PATH
            if not options.print_html:
                print ("searching result files in '{}'...".format(searchDir))
            inputFiles = [os.path.join(searchDir, '*.results*.xml')]

        inputFiles = Util.extend_file_list(inputFiles, options) # expand wildcards
        runSetResults = [RunSetResult.create_from_xml(file, parse_results_file(file, options), options, all_columns=options.all_columns) for file in inputFiles]

        if len(inputFiles) == 1:
            if not name:
                name = basename_without_ending(inputFiles[0])
            outputFilePattern = "{name}.{ext}"
        else:
            if not name:
                name = NAME_START + "." + time.strftime("%Y-%m-%d_%H%M", time.localtime())

        if inputFiles and not outputPath:
            dir = os.path.dirname(inputFiles[0])
            if all(dir == os.path.dirname(file) for file in inputFiles):
                outputPath = dir
            else:
                outputPath = DEFAULT_OUTPUT_PATH

    if not outputPath:
        outputPath = '.'

    if options.ignore_errors:
        filteredRunSets = []
        for runSet in runSetResults:
            if 'error' in runSet.attributes and not options.print_html:
                print('Ignoring benchmark {0} because of error: {1}'
                      .format(", ".join(set(runSet.attributes['name'])),
                              ", ".join(set(runSet.attributes['error']))))
            else:
                filteredRunSets.append(runSet)
        runSetResults = filteredRunSets

    if not runSetResults:
        print ('\nError! No benchmark results found.')
        exit()

    if not options.print_html:
        print ('merging results ...')
    if options.common:
        task_ids = find_common_tasks(runSetResults)
    else:
        # merge list of run sets, so that all run sets contain the same tasks
        task_ids = merge_tasks(runSetResults, options)

    # collect data and find out rows with differences
    if not options.print_html:
        print ('collecting data ...')
    rows     = get_rows(runSetResults, task_ids, options.correct_only, options)
    if not rows:
        print ('Warning: No results found, no tables produced.')
        sys.exit()

    rowsDiff = filter_rows_with_differences(rows, options) if options.write_diff_table else []

    if not options.print_html:
        print ('generating table ...')
    if not os.path.isdir(outputPath): os.makedirs(outputPath)
    create_tables(name, runSetResults, task_ids, rows, rowsDiff, outputPath, outputFilePattern, options)

    if not options.print_html:
        print ('done')

    if options.dump_counts: # print some stats for Buildbot
        print ("REGRESSIONS {}".format(get_regression_count(rows, options.ignoreFlappingTimeouts)))
        countsList = get_counts(rows)
        print ("STATS")
        for counts in countsList:
            print (" ".join(str(e) for e in counts))


if __name__ == '__main__':
    try:
        sys.exit(main())
    except KeyboardInterrupt:
        print ('script was interrupted by user')
        pass
