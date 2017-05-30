#! /usr/bin/env python

from os import path
from multiprocessing.pool import ThreadPool
import multiprocessing
import os
import signal
import logging
import yaml
import psutil
import argparse
from os import path
import subprocess
import re
import glob
import time
import sys

OVERRIDE_FIELDS = ['verifiers', 'memory', 'time-limit', 'memory-limit', 'skip']
APPEND_FIELDS = ['flags']

def bold(text):
  return '\033[1m' + text + '\033[0m'

def red(text, log_file):
  if log_file:
    return text
  else:
    return '\033[0;31m' + text + '\033[0m'

def green(text, log_file):
  if log_file:
    return text
  else:
    return '\033[0;32m' + text + '\033[0m'

def get_result(output):
  if re.search(r'SMACK timed out', output):
    return 'timeout'
  elif re.search(r'SMACK found no errors', output):
    return 'verified'
  elif re.search(r'SMACK found an error', output):
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
    print red("WARNING: @expect MISSING IN %s" % file, None)
    m['expect'] = 'verified'

  return m

# integer constants
PASSED = 0; TIMEDOUT = 1; UNKNOWN = 2; FAILED = -1;
def process_test(cmd, test, memory, verifier, expect, log_file):
  """
  This is the worker function for each process. This function process the supplied
  test and returns a tuple containing  indicating the test results.

  :return: A tuple with the
  """
  str_result = "{0:>20}\n".format(test)
  str_result += "{0:>20} {1:>10}    :".format(memory, verifier)

  t0 = time.time()
  p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
  out, err  = p.communicate()
  elapsed = time.time() - t0

  # get the test results
  result = get_result(out+err)
  if result == expect:
    str_result += green('PASSED ', log_file)
  elif result == 'timeout':
    str_result += red('TIMEOUT', log_file)
  elif result == 'unknown':
    str_result += red('UNKNOWN', log_file)
  else:
    str_result += red('FAILED ', log_file)

  str_result += '  [%.2fs]' % round(elapsed, 2)
  return str_result

passed = failed = timeouts = unknowns = 0
def tally_result(result):
  """
  Tallies the result of each worker. This will only be called by the main thread.
  """
  # log the info
  logging.info(result)

  global passed, failed, timeouts, unknowns
  if "PASSED" in result:
    passed += 1
  elif "FAILED" in result:
    failed += 1
  elif "TIMEOUT" in result:
    timeouts += 1
  elif "UNKNOWN" in result:
    unknowns += 1

def main():
  """
  Main entry point for the test suite.
  """
  t0 = time.time()
  num_cpus = multiprocessing.cpu_count()
  mem_total = psutil.virtual_memory().total / (1024 * 1024)

  # configure the CLI
  parser = argparse.ArgumentParser()
  parser.add_argument("--exhaustive", help="check all configurations on all examples", action="store_true")
  parser.add_argument("--all-configs", help="check all configurations per example", action="store_true")
  parser.add_argument("--all-examples", help="check all examples", action="store_true")
  parser.add_argument("--folder", action="store", default="**", type=str,
                      help="sets the regressions folder to run")
  parser.add_argument("--threads", action="store", dest="n_threads", default=num_cpus, type=int,
                      help="execute regressions using the selected number of threads in parallel")
  parser.add_argument("--log", action="store", dest="log_level", default="DEBUG", type=str,
                      help="sets the logging level (DEBUG, INFO, WARNING)")
  parser.add_argument("--output-log", action="store", dest="log_path", type=str,
                      help="sets the output log path. (std out by default)")
  args = parser.parse_args()

  if args.exhaustive:
    args.all_examples = True;
    args.all_configs = True;

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

  try:
    # start the tests
    logging.info("Running regression tests...")

    # start processing the tests.
    results = []
    for test in sorted(glob.glob("./" + args.folder + "/*.c")):
      # get the meta data for this test
      meta = metadata(test)

      if meta['memory-limit'] > mem_total:
        continue

      if meta['skip'] == True:
        continue

      if meta['skip'] != False and not args.all_examples:
        continue

      # build up the subprocess command
      cmd = ['smack', test]
      cmd += ['--time-limit', str(meta['time-limit'])]
      cmd += meta['flags']

      for memory in meta['memory'][:100 if args.all_configs else 1]:
        cmd += ['--mem-mod=' + memory]

        for verifier in meta['verifiers'][:100 if args.all_configs else 1]:
          name = path.splitext(path.basename(test))[0]
          cmd += ['--verifier=' + verifier]
          cmd += ['-bc', "%s-%s-%s.bc" % (name, memory, verifier)]
          cmd += ['-bpl', "%s-%s-%s.bpl" % (name, memory, verifier)]
          r = p.apply_async(process_test,
                args=(cmd[:], test, memory, verifier, meta['expect'], args.log_path,),
                callback=tally_result)
          results.append(r)

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

  # log the test results
  logging.info(' PASSED count: %d' % passed)
  logging.info(' FAILED count: %d' % failed)
  logging.info(' TIMEOUT count: %d' % timeouts)
  logging.info(' UNKNOWN count: %d' % unknowns)

  # if there are any failed tests or tests that timed out, set the system
  # exit code to a failure status
  if timeouts > 0 or failed > 0 or unknowns > 0:
    sys.exit(1)

if __name__=="__main__":
  main()
