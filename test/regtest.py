#! /usr/bin/env python

from os import path
from multiprocessing.pool import ThreadPool
import multiprocessing
import os
import signal
import logging
import yaml
import argparse
from os import path
import subprocess
import re
import glob
import time
import sys

OVERRIDE_FIELDS = ['verifiers', 'memory', 'time-limit', 'skip']
APPEND_FIELDS = ['flags']

# integer constants
PASSED = 0
TIMEDOUT = 1
UNKNOWN = 2
FAILED = -1

def red(text):
  return '\033[0;31m' + text + '\033[0m'
  
def green(text):
  return '\033[0;32m' + text + '\033[0m'

def get_result(output):
  if re.search(r'[1-9]\d* time out|Z3 ran out of resources|z3 timed out|Corral timed out', output):
    return 'timeout'
  elif re.search(r'[1-9]\d* verified, 0 errors?|no bugs', output):
    return 'verified'
  elif re.search(r'0 verified, [1-9]\d* errors?|can fail', output):
    return 'error'
  else:
    return 'unknown'

def merge(metadata, yamldata):
  for key in OVERRIDE_FIELDS:
    if key in yamldata:
      metadata[key] = yamldata[key]

  for key in APPEND_FIELDS:
    if key in yamldata:
      if key in metadata:
        metadata[key] += yamldata[key]
      else:
        metadata[key] = yamldata[key]

def metadata(file):
  m = {}
  prefix = []

  for d in path.dirname(file).split('/'):
    prefix += [d]
    yaml_file = path.join(*(prefix + ['config.yml']))
    if path.isfile(yaml_file):
      with open(yaml_file, "r") as f:
        data = yaml.safe_load(f)
        merge(m,data)

  with open(file, "r") as f:
    for line in f.readlines():

      match = re.search(r'@skip', line)
      if match:
        m['skip'] = True

      match = re.search(r'@flag (.*)',line)
      if match:
        m['flags'] += [match.group(1).strip()]

      match = re.search(r'@expect (.*)',line)
      if match:
        m['expect'] = match.group(1).strip()

  if not m['skip'] and not 'expect' in m:
    print red("WARNING: @expect MISSING IN %s" % file)
    m['expect'] = 'verified'

  return m
  
parser = argparse.ArgumentParser()
parser.add_argument("--exhaustive", help="be exhaustive", action="store_true")
args = parser.parse_args()

def process_test(cmd, test, memory, verifier, meta):
    """
    This is the worker function for each process. This function process the supplied
    test and returns an integer indicating the test results.

    :return: 0 (PASSED), -1 (FAILED), 1 (TIMEDOUT), 2 (UNKNOWN)
    """
    str_result = "{0:>20}\n".format(test)
    str_result += "{0:>20} {1:>10}    :".format(memory, verifier)

    t0 = time.time()
    p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    out, err  = p.communicate()
    elapsed = time.time() - t0

    # get the test results
    result = get_result(out+err)
    passed = timedout = unknown = False
    if result == meta['expect']:
      str_result += 'PASSED '
      passed = True

    elif result == 'timeout':
      str_result += 'TIMEOUT'
      timedout = True

    elif result == 'unknown':
      str_result += 'UNKNOWN'
      unknown = True

    else:
      str_result += 'FAILED '

    str_result += '  [%.2fs]' % round(elapsed, 2)

    # log the info for this test
    logging.info(str_result)

    # returns a status code based on the results of the test
    if passed:
      return PASSED
    elif timedout:
      return TIMEDOUT
    elif unknown:
      return UNKNOWN
    else:
      return FAILED

test_results = []
def tally_result(result):
    """
    Called whenever a worker has finished its process. Only the main process
    will modify test_results.
    """
    test_results.append(result)

def main():
    """
    Main entry point for the test suite.
    """
    t0 = time.time()
    num_cpus = multiprocessing.cpu_count()

    # configure the CLI
    parser = argparse.ArgumentParser()
    parser.add_argument("--exhaustive", help="be exhaustive", action="store_true")
    parser.add_argument("--threads", action="store", dest="n_threads", default=num_cpus, type=int,
                        help="execute regressions using the selected number of threads in parallel")
    parser.add_argument("--log", action="store", dest="log_level", default="DEBUG", type=str,
                        help="sets the logging level (DEBUG, INFO, WARNING)")
    parser.add_argument("--output_log", action="store", dest="log_path", type=str,
                        help="sets the output log path. (std out by default)")
    args = parser.parse_args()


    # configure the logging
    log_format = ''
    log_level = logging.DEBUG

    # add more log levels later (if needed)
    if args.log_level.upper() == "INFO":
      log_level = logging.INFO
    elif args.log_level.upper() == "WARNING":
      log_level = logging.WARNING

    # if the user supplied a log path, write the logs to that file.
    # otherwise, write the logs to std out.
    if args.log_path:
      logging.basicConfig(filename=args.log_path, format=log_format, level=log_level)
    else:
      logging.basicConfig(format=log_format, level=log_level)

    logging.debug("Creating Pool with '%d' Workers" % args.n_threads)
    p = ThreadPool(processes=args.n_threads)

    # start the tests
    logging.info("Running regression tests...")

    # start processing the tests.
    results = []
    for test in glob.glob("./**/*.c"):
      # get the meta data for this test
      meta = metadata(test)

      if meta['skip']:
        continue

      if meta['skip'] != False and not args.exhaustive:
        continue

      # build up the subprocess command
      cmd = ['smackverify.py', test]
      cmd += ['--time-limit', str(meta['time-limit'])]
      cmd += ['-o', test + '.bpl']
      cmd += meta['flags']

      for memory in meta['memory'][:100 if args.exhaustive else 1]:
        cmd += ['--mem-mod=' + memory]

        for verifier in meta['verifiers'][:100 if args.exhaustive else 1]:
          cmd += ['--verifier=' + verifier]
          r = p.apply_async(process_test, args=(cmd, test, memory, verifier, meta,), callback=tally_result)
          results.append(r)

    try:
      # keep the main thread active while there are active workers
      for r in results:
        r.wait()

    except KeyboardInterrupt:
      logging.debug("Caught KeyboardInterrupt, terminating workers")
      p.terminate() # terminate any remaining workers
      p.join()
    else:
      logging.debug("Quitting normally")
      # close the pool. this prevents any more tasks from being submitted.
      p.close()
      p.join() # wait for all workers to finish their tasks

    # log the elapsed time
    elapsed_time = time.time() - t0
    logging.info(' ELAPSED TIME [%.2fs]' % round(elapsed_time, 2))

    # tally up the results
    passed = failed = timeouts = unknowns = 0
    for r in test_results:
      if r == PASSED:
        passed += 1
      elif r == TIMEDOUT:
        timeouts += 1
      elif r == UNKNOWN:
        unknowns += 1
      elif r == FAILED:
        failed += 1

    # log the test results
    logging.info(' PASSED count: %d' % passed)
    logging.info(' FAILED count: %d' % failed)
    logging.info(' TIMEOUT count: %d' % timeouts)
    logging.info(' UNKNOWN count: %d' % unknowns)

if __name__=="__main__":
    main()
